/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004, 2012 Artois University and CNRS
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 *  http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 *
 * Based on the original MiniSat specification from:
 *
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 *
 * Contributors:
 *   CRIL - initial API and implementation
 *******************************************************************************/
package org.sat4j.minisat.constraints.cnf;

import static org.sat4j.core.LiteralsUtils.neg;
import static org.sat4j.core.LiteralsUtils.var;

import java.io.Serializable;

import org.sat4j.annotations.Feature;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.core.ILits;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.Propagatable;
import org.sat4j.specs.UnitPropagationListener;
import org.sat4j.specs.VarMapper;

/**
 * Lazy data structure for clause using the Head Tail data structure from SATO,
 * The original scheme is improved by avoiding moving pointers to literals but
 * moving the literals themselves.
 * 
 * We suppose here that the clause contains at least 3 literals. Use the
 * BinaryClause or UnaryClause clause data structures to deal with binary and
 * unit clauses.
 * 
 * @author leberre
 * @see BinaryClause
 * @see UnitClause
 * @since 2.1
 */
@Feature("constraint")
public abstract class HTClause implements Propagatable, Constr, Serializable {

    private static final long serialVersionUID = 1L;

    protected double activity;

    protected final int[] middleLits;

    protected final ILits voc;

    protected int head;

    protected int tail;

    /**
     * Creates a new basic clause
     * 
     * @param voc
     *            the vocabulary of the formula
     * @param ps
     *            A VecInt that WILL BE EMPTY after calling that method.
     */
    public HTClause(IVecInt ps, ILits voc) {
        assert ps.size() > 1;
        this.head = ps.get(0);
        this.tail = ps.last();
        final int size = ps.size() - 2;
        assert size > 0;
        this.middleLits = new int[size];
        System.arraycopy(ps.toArray(), 1, this.middleLits, 0, size);
        ps.clear();
        assert ps.size() == 0;
        this.voc = voc;
        this.activity = 0;
    }

    /*
     * (non-Javadoc)
     * 
     * @see Constr#calcReason(Solver, Lit, Vec)
     */
    public void calcReason(int p, IVecInt outReason) {
        if (this.voc.isFalsified(this.head)) {
            outReason.push(neg(this.head));
        }
        final int[] mylits = this.middleLits;
        for (int mylit : mylits) {
            if (this.voc.isFalsified(mylit)) {
                outReason.push(neg(mylit));
            }
        }
        if (this.voc.isFalsified(this.tail)) {
            outReason.push(neg(this.tail));
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see Constr#remove(Solver)
     */
    public void remove(UnitPropagationListener upl) {
        this.voc.watches(neg(this.head)).remove(this);
        this.voc.watches(neg(this.tail)).remove(this);
    }

    /*
     * (non-Javadoc)
     * 
     * @see Constr#simplify(Solver)
     */
    public boolean simplify() {
        if (this.voc.isSatisfied(this.head)
                || this.voc.isSatisfied(this.tail)) {
            return true;
        }
        for (int middleLit : this.middleLits) {
            if (this.voc.isSatisfied(middleLit)) {
                return true;
            }
        }
        return false;
    }

    public boolean propagate(UnitPropagationListener s, int p) {

        if (this.head == neg(p)) {
            final int[] mylits = this.middleLits;
            int temphead = 0;
            // moving head on the right
            while (temphead < mylits.length
                    && this.voc.isFalsified(mylits[temphead])) {
                temphead++;
            }
            assert temphead <= mylits.length;
            if (temphead == mylits.length) {
                this.voc.watch(p, this);
                return s.enqueue(this.tail, this);
            }
            this.head = mylits[temphead];
            mylits[temphead] = neg(p);
            this.voc.watch(neg(this.head), this);
            return true;
        }
        assert this.tail == neg(p);
        final int[] mylits = this.middleLits;
        int temptail = mylits.length - 1;
        // moving tail on the left
        while (temptail >= 0 && this.voc.isFalsified(mylits[temptail])) {
            temptail--;
        }
        assert -1 <= temptail;
        if (-1 == temptail) {
            this.voc.watch(p, this);
            return s.enqueue(this.head, this);
        }
        this.tail = mylits[temptail];
        mylits[temptail] = neg(p);
        this.voc.watch(neg(this.tail), this);
        return true;
    }

    /*
     * For learnt clauses only @author leberre
     */
    public boolean locked() {
        return this.voc.getReason(this.head) == this
                || this.voc.getReason(this.tail) == this;
    }

    /**
     * @return the activity of the clause
     */
    public double getActivity() {
        return this.activity;
    }

    @Override
    public String toString() {
        StringBuilder stb = new StringBuilder();
        stb.append(Lits.toString(this.head));
        stb.append("["); //$NON-NLS-1$
        stb.append(this.voc.valueToString(this.head));
        stb.append("]"); //$NON-NLS-1$
        stb.append(" "); //$NON-NLS-1$
        for (int middleLit : this.middleLits) {
            stb.append(Lits.toString(middleLit));
            stb.append("["); //$NON-NLS-1$
            stb.append(this.voc.valueToString(middleLit));
            stb.append("]"); //$NON-NLS-1$
            stb.append(" "); //$NON-NLS-1$
        }
        stb.append(Lits.toString(this.tail));
        stb.append("["); //$NON-NLS-1$
        stb.append(this.voc.valueToString(this.tail));
        stb.append("]"); //$NON-NLS-1$
        return stb.toString();
    }

    /**
     * Return the ith literal of the clause. Note that the order of the literals
     * does change during the search...
     * 
     * @param i
     *            the index of the literal
     * @return the literal
     */
    public int get(int i) {
        if (i == 0) {
            return this.head;
        }
        if (i == this.middleLits.length + 1) {
            return this.tail;
        }
        return this.middleLits[i - 1];
    }

    /**
     * @param d
     */
    public void rescaleBy(double d) {
        this.activity *= d;
    }

    public int size() {
        return this.middleLits.length + 2;
    }

    public void assertConstraint(UnitPropagationListener s) {
        assert this.voc.isUnassigned(this.head);
        boolean ret = s.enqueue(this.head, this);
        assert ret;
    }

    public void assertConstraintIfNeeded(UnitPropagationListener s) {
        if (voc.isFalsified(this.tail)) {
            boolean ret = s.enqueue(this.head, this);
            assert ret;
        }
    }

    public ILits getVocabulary() {
        return this.voc;
    }

    public int[] getLits() {
        int[] tmp = new int[size()];
        System.arraycopy(this.middleLits, 0, tmp, 1, this.middleLits.length);
        tmp[0] = this.head;
        tmp[tmp.length - 1] = this.tail;
        return tmp;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass())
            return false;
        try {
            HTClause wcl = (HTClause) obj;
            if (wcl.head != this.head || wcl.tail != this.tail) {
                return false;
            }
            if (this.middleLits.length != wcl.middleLits.length) {
                return false;
            }
            boolean ok;
            for (int lit : this.middleLits) {
                ok = false;
                for (int lit2 : wcl.middleLits) {
                    if (lit == lit2) {
                        ok = true;
                        break;
                    }
                }
                if (!ok) {
                    return false;
                }
            }
            return true;
        } catch (ClassCastException e) {
            return false;
        }
    }

    @Override
    public int hashCode() {
        long sum = (long) this.head + this.tail;
        for (int p : this.middleLits) {
            sum += p;
        }
        return (int) sum / this.middleLits.length;
    }

    public boolean canBePropagatedMultipleTimes() {
        return false;
    }

    public Constr toConstraint() {
        return this;
    }

    public void calcReasonOnTheFly(int p, IVecInt trail, IVecInt outReason) {
        calcReason(p, outReason);
    }

    public boolean canBeSatisfiedByCountingLiterals() {
        return true;
    }

    public int requiredNumberOfSatisfiedLiterals() {
        return 1;
    }

    public boolean isSatisfied() {
        if (voc.isSatisfied(this.head))
            return true;
        if (voc.isSatisfied(this.tail))
            return true;
        for (int p : this.middleLits) {
            if (voc.isSatisfied(p))
                return true;
        }
        return false;
    }

    public int getAssertionLevel(IVecInt trail, int decisionLevel) {
        for (int i = trail.size() - 1; i >= 0; i--) {
            if (var(trail.get(i)) == var(this.head)) {
                return i;
            }
        }
        return -1;
    }

    public String toString(VarMapper mapper) {
        StringBuilder stb = new StringBuilder();
        stb.append(mapper.map(LiteralsUtils.toDimacs(this.head)));
        stb.append("["); //$NON-NLS-1$
        stb.append(this.voc.valueToString(this.head));
        stb.append("]"); //$NON-NLS-1$
        stb.append(" "); //$NON-NLS-1$
        for (int middleLit : this.middleLits) {
            stb.append(mapper.map(LiteralsUtils.toDimacs(middleLit)));
            stb.append("["); //$NON-NLS-1$
            stb.append(this.voc.valueToString(middleLit));
            stb.append("]"); //$NON-NLS-1$
            stb.append(" "); //$NON-NLS-1$
        }
        stb.append(mapper.map(LiteralsUtils.toDimacs(this.tail)));
        stb.append("["); //$NON-NLS-1$
        stb.append(this.voc.valueToString(this.tail));
        stb.append("]"); //$NON-NLS-1$
        return stb.toString();
    }

    @Override
    public String dump() {
        StringBuilder stb = new StringBuilder();
        stb.append(LiteralsUtils.toDimacs(this.head));
        stb.append(' ');
        for (int p : middleLits) {
            stb.append(LiteralsUtils.toDimacs(p));
            stb.append(' ');
        }
        stb.append(LiteralsUtils.toDimacs(this.tail));
        stb.append(" 0");
        return stb.toString();
    }

}
