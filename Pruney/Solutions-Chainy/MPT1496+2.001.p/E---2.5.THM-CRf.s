%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:58 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 413 expanded)
%              Number of clauses        :   20 ( 128 expanded)
%              Number of leaves         :    5 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 (2076 expanded)
%              Number of equality atoms :    8 (  48 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t29_lattice3,conjecture,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(k3_lattice3(X2)))
         => ( r1_lattice3(k3_lattice3(X2),X1,X3)
          <=> r3_lattice3(X2,k5_lattice3(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_lattice3)).

fof(d4_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))
         => k5_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).

fof(dt_k5_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) )
     => m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).

fof(d3_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattice3(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

fof(t28_lattice3,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & l3_lattices(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,u1_struct_0(X2))
         => ( r3_lattice3(X2,X3,X1)
          <=> r1_lattice3(k3_lattice3(X2),X1,k4_lattice3(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_lattice3)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( ~ v2_struct_0(X2)
          & v10_lattices(X2)
          & l3_lattices(X2) )
       => ! [X3] :
            ( m1_subset_1(X3,u1_struct_0(k3_lattice3(X2)))
           => ( r1_lattice3(k3_lattice3(X2),X1,X3)
            <=> r3_lattice3(X2,k5_lattice3(X2,X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t29_lattice3])).

fof(c_0_6,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v10_lattices(X6)
      | ~ l3_lattices(X6)
      | ~ m1_subset_1(X7,u1_struct_0(k3_lattice3(X6)))
      | k5_lattice3(X6,X7) = X7 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattice3])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v10_lattices(esk2_0)
    & l3_lattices(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(esk2_0)))
    & ( ~ r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)
      | ~ r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0) )
    & ( r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)
      | r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X8,X9] :
      ( v2_struct_0(X8)
      | ~ v10_lattices(X8)
      | ~ l3_lattices(X8)
      | ~ m1_subset_1(X9,u1_struct_0(k3_lattice3(X8)))
      | m1_subset_1(k5_lattice3(X8,X9),u1_struct_0(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattice3])])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | k5_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l3_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v10_lattices(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_14,plain,(
    ! [X4,X5] :
      ( v2_struct_0(X4)
      | ~ v10_lattices(X4)
      | ~ l3_lattices(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | k4_lattice3(X4,X5) = X5 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( k5_lattice3(esk2_0,esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])]),c_0_13])).

fof(c_0_17,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r3_lattice3(X11,X12,X10)
        | r1_lattice3(k3_lattice3(X11),X10,k4_lattice3(X11,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( ~ r1_lattice3(k3_lattice3(X11),X10,k4_lattice3(X11,X12))
        | r3_lattice3(X11,X12,X10)
        | ~ m1_subset_1(X12,u1_struct_0(X11))
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_lattice3])])])])])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | k4_lattice3(X1,X2) = X2
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_10]),c_0_11]),c_0_12])]),c_0_13]),c_0_16])).

cnf(c_0_20,plain,
    ( r3_lattice3(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(k3_lattice3(X1),X2,k4_lattice3(X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( r1_lattice3(k3_lattice3(X1),X3,k4_lattice3(X1,X2))
    | v2_struct_0(X1)
    | ~ r3_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( k4_lattice3(esk2_0,esk3_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,X1)
    | ~ r1_lattice3(k3_lattice3(esk2_0),X1,k4_lattice3(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_19]),c_0_11]),c_0_12])]),c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)
    | r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk2_0),X1,esk3_0)
    | ~ r3_lattice3(esk2_0,esk3_0,X1) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_11]),c_0_12])]),c_0_13]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,X1)
    | ~ r1_lattice3(k3_lattice3(esk2_0),X1,esk3_0) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_16]),c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)
    | ~ r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( r3_lattice3(esk2_0,esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_16]),c_0_27]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic H_____047_C18_F1_PI_AE_R8_CS_SP_S2S
% 0.19/0.38  # and selection function SelectNewComplexAHP.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t29_lattice3, conjecture, ![X1, X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_lattice3(X2)))=>(r1_lattice3(k3_lattice3(X2),X1,X3)<=>r3_lattice3(X2,k5_lattice3(X2,X3),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_lattice3)).
% 0.19/0.38  fof(d4_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))=>k5_lattice3(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_lattice3)).
% 0.19/0.38  fof(dt_k5_lattice3, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(k3_lattice3(X1))))=>m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattice3)).
% 0.19/0.38  fof(d3_lattice3, axiom, ![X1]:(((~(v2_struct_0(X1))&v10_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattice3(X1,X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattice3)).
% 0.19/0.38  fof(t28_lattice3, axiom, ![X1, X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>(r3_lattice3(X2,X3,X1)<=>r1_lattice3(k3_lattice3(X2),X1,k4_lattice3(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_lattice3)).
% 0.19/0.38  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(((~(v2_struct_0(X2))&v10_lattices(X2))&l3_lattices(X2))=>![X3]:(m1_subset_1(X3,u1_struct_0(k3_lattice3(X2)))=>(r1_lattice3(k3_lattice3(X2),X1,X3)<=>r3_lattice3(X2,k5_lattice3(X2,X3),X1))))), inference(assume_negation,[status(cth)],[t29_lattice3])).
% 0.19/0.38  fof(c_0_6, plain, ![X6, X7]:(v2_struct_0(X6)|~v10_lattices(X6)|~l3_lattices(X6)|(~m1_subset_1(X7,u1_struct_0(k3_lattice3(X6)))|k5_lattice3(X6,X7)=X7)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_lattice3])])])])).
% 0.19/0.38  fof(c_0_7, negated_conjecture, (((~v2_struct_0(esk2_0)&v10_lattices(esk2_0))&l3_lattices(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(esk2_0)))&((~r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)|~r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0))&(r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)|r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.19/0.38  fof(c_0_8, plain, ![X8, X9]:(v2_struct_0(X8)|~v10_lattices(X8)|~l3_lattices(X8)|~m1_subset_1(X9,u1_struct_0(k3_lattice3(X8)))|m1_subset_1(k5_lattice3(X8,X9),u1_struct_0(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattice3])])])).
% 0.19/0.38  cnf(c_0_9, plain, (v2_struct_0(X1)|k5_lattice3(X1,X2)=X2|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.38  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(k3_lattice3(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_11, negated_conjecture, (l3_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_12, negated_conjecture, (v10_lattices(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  fof(c_0_14, plain, ![X4, X5]:(v2_struct_0(X4)|~v10_lattices(X4)|~l3_lattices(X4)|(~m1_subset_1(X5,u1_struct_0(X4))|k4_lattice3(X4,X5)=X5)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_lattice3])])])])).
% 0.19/0.38  cnf(c_0_15, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattice3(X1,X2),u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(k3_lattice3(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (k5_lattice3(esk2_0,esk3_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.38  fof(c_0_17, plain, ![X10, X11, X12]:((~r3_lattice3(X11,X12,X10)|r1_lattice3(k3_lattice3(X11),X10,k4_lattice3(X11,X12))|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~v10_lattices(X11)|~l3_lattices(X11)))&(~r1_lattice3(k3_lattice3(X11),X10,k4_lattice3(X11,X12))|r3_lattice3(X11,X12,X10)|~m1_subset_1(X12,u1_struct_0(X11))|(v2_struct_0(X11)|~v10_lattices(X11)|~l3_lattices(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t28_lattice3])])])])])).
% 0.19/0.38  cnf(c_0_18, plain, (v2_struct_0(X1)|k4_lattice3(X1,X2)=X2|~v10_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_10]), c_0_11]), c_0_12])]), c_0_13]), c_0_16])).
% 0.19/0.38  cnf(c_0_20, plain, (r3_lattice3(X1,X3,X2)|v2_struct_0(X1)|~r1_lattice3(k3_lattice3(X1),X2,k4_lattice3(X1,X3))|~m1_subset_1(X3,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_21, plain, (r1_lattice3(k3_lattice3(X1),X3,k4_lattice3(X1,X2))|v2_struct_0(X1)|~r3_lattice3(X1,X2,X3)|~m1_subset_1(X2,u1_struct_0(X1))|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (k4_lattice3(esk2_0,esk3_0)=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (r3_lattice3(esk2_0,esk3_0,X1)|~r1_lattice3(k3_lattice3(esk2_0),X1,k4_lattice3(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_19]), c_0_11]), c_0_12])]), c_0_13])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)|r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r1_lattice3(k3_lattice3(esk2_0),X1,esk3_0)|~r3_lattice3(esk2_0,esk3_0,X1)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_11]), c_0_12])]), c_0_13]), c_0_22])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (r3_lattice3(esk2_0,esk3_0,X1)|~r1_lattice3(k3_lattice3(esk2_0),X1,esk3_0)), inference(rw,[status(thm)],[c_0_23, c_0_22])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_16]), c_0_25])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (~r1_lattice3(k3_lattice3(esk2_0),esk1_0,esk3_0)|~r3_lattice3(esk2_0,k5_lattice3(esk2_0,esk3_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (r3_lattice3(esk2_0,esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_16]), c_0_27]), c_0_29])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 31
% 0.19/0.38  # Proof object clause steps            : 20
% 0.19/0.38  # Proof object formula steps           : 11
% 0.19/0.38  # Proof object conjectures             : 18
% 0.19/0.38  # Proof object clause conjectures      : 15
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 11
% 0.19/0.38  # Proof object initial formulas used   : 5
% 0.19/0.38  # Proof object generating inferences   : 6
% 0.19/0.38  # Proof object simplifying inferences  : 29
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 5
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 11
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 11
% 0.19/0.38  # Processed clauses                    : 22
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 21
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 3
% 0.19/0.38  # Generated clauses                    : 10
% 0.19/0.38  # ...of the previous two non-trivial   : 12
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 10
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 18
% 0.19/0.38  #    Positive orientable unit clauses  : 8
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 9
% 0.19/0.38  # Current number of unprocessed clauses: 1
% 0.19/0.38  # ...number of literals in the above   : 5
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 3
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 17
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 1
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.38  # Unit Clause-clause subsumption calls : 2
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 3
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 1368
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.029 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.032 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
