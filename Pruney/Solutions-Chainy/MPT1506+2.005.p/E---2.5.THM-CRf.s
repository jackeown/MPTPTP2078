%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:01 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   20 (  38 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 235 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   40 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( X2 = k16_lattice3(X1,X3)
            <=> ( r3_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r3_lattice3(X1,X4,X3)
                     => r3_lattices(X1,X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(dt_k16_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(t40_lattice3,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v4_lattice3(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( r3_lattice3(X1,X2,X3)
             => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

fof(c_0_3,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( r3_lattice3(X7,X8,X9)
        | X8 != k16_lattice3(X7,X9)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ v4_lattice3(X7)
        | ~ l3_lattices(X7) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r3_lattice3(X7,X10,X9)
        | r3_lattices(X7,X10,X8)
        | X8 != k16_lattice3(X7,X9)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ v4_lattice3(X7)
        | ~ l3_lattices(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))
        | ~ r3_lattice3(X7,X8,X11)
        | X8 = k16_lattice3(X7,X11)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ v4_lattice3(X7)
        | ~ l3_lattices(X7) )
      & ( r3_lattice3(X7,esk1_3(X7,X8,X11),X11)
        | ~ r3_lattice3(X7,X8,X11)
        | X8 = k16_lattice3(X7,X11)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ v4_lattice3(X7)
        | ~ l3_lattices(X7) )
      & ( ~ r3_lattices(X7,esk1_3(X7,X8,X11),X8)
        | ~ r3_lattice3(X7,X8,X11)
        | X8 = k16_lattice3(X7,X11)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | v2_struct_0(X7)
        | ~ v10_lattices(X7)
        | ~ v4_lattice3(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).

fof(c_0_4,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | m1_subset_1(k16_lattice3(X5,X6),u1_struct_0(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v4_lattice3(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( r3_lattice3(X1,X2,X3)
               => r3_lattices(X1,X2,k16_lattice3(X1,X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t40_lattice3])).

cnf(c_0_6,plain,
    ( r3_lattices(X2,X1,X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r3_lattice3(X2,X1,X3)
    | X4 != k16_lattice3(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v10_lattices(X2)
    | ~ v4_lattice3(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & v4_lattice3(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & r3_lattice3(esk2_0,esk3_0,esk4_0)
    & ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_9,plain,
    ( r3_lattices(X1,X2,k16_lattice3(X1,X3))
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ v4_lattice3(X1)
    | ~ v10_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_6]),c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v4_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r3_lattices(esk2_0,X1,k16_lattice3(esk2_0,X2))
    | ~ r3_lattice3(esk2_0,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))
    | ~ r3_lattice3(esk2_0,esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( ~ r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:23:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.14/0.38  # and selection function SelectCQIAr.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t34_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(X2=k16_lattice3(X1,X3)<=>(r3_lattice3(X1,X2,X3)&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r3_lattice3(X1,X4,X3)=>r3_lattices(X1,X4,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 0.14/0.38  fof(dt_k16_lattice3, axiom, ![X1, X2]:((~(v2_struct_0(X1))&l3_lattices(X1))=>m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 0.14/0.38  fof(t40_lattice3, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)=>r3_lattices(X1,X2,k16_lattice3(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 0.14/0.38  fof(c_0_3, plain, ![X7, X8, X9, X10, X11]:(((r3_lattice3(X7,X8,X9)|X8!=k16_lattice3(X7,X9)|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v10_lattices(X7)|~v4_lattice3(X7)|~l3_lattices(X7)))&(~m1_subset_1(X10,u1_struct_0(X7))|(~r3_lattice3(X7,X10,X9)|r3_lattices(X7,X10,X8))|X8!=k16_lattice3(X7,X9)|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v10_lattices(X7)|~v4_lattice3(X7)|~l3_lattices(X7))))&((m1_subset_1(esk1_3(X7,X8,X11),u1_struct_0(X7))|~r3_lattice3(X7,X8,X11)|X8=k16_lattice3(X7,X11)|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v10_lattices(X7)|~v4_lattice3(X7)|~l3_lattices(X7)))&((r3_lattice3(X7,esk1_3(X7,X8,X11),X11)|~r3_lattice3(X7,X8,X11)|X8=k16_lattice3(X7,X11)|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v10_lattices(X7)|~v4_lattice3(X7)|~l3_lattices(X7)))&(~r3_lattices(X7,esk1_3(X7,X8,X11),X8)|~r3_lattice3(X7,X8,X11)|X8=k16_lattice3(X7,X11)|~m1_subset_1(X8,u1_struct_0(X7))|(v2_struct_0(X7)|~v10_lattices(X7)|~v4_lattice3(X7)|~l3_lattices(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_lattice3])])])])])])])).
% 0.14/0.38  fof(c_0_4, plain, ![X5, X6]:(v2_struct_0(X5)|~l3_lattices(X5)|m1_subset_1(k16_lattice3(X5,X6),u1_struct_0(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k16_lattice3])])])).
% 0.14/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v4_lattice3(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(r3_lattice3(X1,X2,X3)=>r3_lattices(X1,X2,k16_lattice3(X1,X3)))))), inference(assume_negation,[status(cth)],[t40_lattice3])).
% 0.14/0.38  cnf(c_0_6, plain, (r3_lattices(X2,X1,X4)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r3_lattice3(X2,X1,X3)|X4!=k16_lattice3(X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v10_lattices(X2)|~v4_lattice3(X2)|~l3_lattices(X2)), inference(split_conjunct,[status(thm)],[c_0_3])).
% 0.14/0.38  cnf(c_0_7, plain, (v2_struct_0(X1)|m1_subset_1(k16_lattice3(X1,X2),u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ((((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&v4_lattice3(esk2_0))&l3_lattices(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(r3_lattice3(esk2_0,esk3_0,esk4_0)&~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.14/0.38  cnf(c_0_9, plain, (r3_lattices(X1,X2,k16_lattice3(X1,X3))|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~v4_lattice3(X1)|~v10_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~l3_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_6]), c_0_7])).
% 0.14/0.38  cnf(c_0_10, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (v4_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (r3_lattices(esk2_0,X1,k16_lattice3(esk2_0,X2))|~r3_lattice3(esk2_0,X1,X2)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,X1))|~r3_lattice3(esk2_0,esk3_0,X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (r3_lattice3(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (~r3_lattices(esk2_0,esk3_0,k16_lattice3(esk2_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 20
% 0.14/0.38  # Proof object clause steps            : 13
% 0.14/0.38  # Proof object formula steps           : 7
% 0.14/0.38  # Proof object conjectures             : 13
% 0.14/0.38  # Proof object clause conjectures      : 10
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 9
% 0.14/0.38  # Proof object initial formulas used   : 3
% 0.14/0.38  # Proof object generating inferences   : 3
% 0.14/0.38  # Proof object simplifying inferences  : 7
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 3
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 13
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 13
% 0.14/0.38  # Processed clauses                    : 30
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 30
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 9
% 0.14/0.38  # ...of the previous two non-trivial   : 8
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 7
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 15
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 6
% 0.14/0.38  # Current number of unprocessed clauses: 4
% 0.14/0.38  # ...number of literals in the above   : 22
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 13
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 31
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 3
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1322
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.031 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
