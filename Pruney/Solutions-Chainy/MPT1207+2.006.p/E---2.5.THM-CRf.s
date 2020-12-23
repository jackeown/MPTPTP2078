%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:26 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 224 expanded)
%              Number of clauses        :   30 (  73 expanded)
%              Number of leaves         :    8 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 (1201 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(t40_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k4_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(t21_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattices(X1,X2,X3)
              <=> k2_lattices(X1,X2,X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(redefinition_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X2,X3)
      <=> r1_lattices(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r3_lattices(X1,k5_lattices(X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t41_lattices])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( v2_struct_0(X7)
      | ~ v6_lattices(X7)
      | ~ l1_lattices(X7)
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | k4_lattices(X7,X8,X9) = k2_lattices(X7,X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v13_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ~ r3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X5] :
      ( v2_struct_0(X5)
      | ~ l1_lattices(X5)
      | m1_subset_1(k5_lattices(X5),u1_struct_0(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_12,plain,(
    ! [X6] :
      ( ( l1_lattices(X6)
        | ~ l3_lattices(X6) )
      & ( l2_lattices(X6)
        | ~ l3_lattices(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( v2_struct_0(X16)
      | ~ v10_lattices(X16)
      | ~ v13_lattices(X16)
      | ~ l3_lattices(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | k4_lattices(X16,k5_lattices(X16),X17) = k5_lattices(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattices])])])])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1)
    | ~ v10_lattices(X1)
    | ~ v13_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v13_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( k4_lattices(esk1_0,X1,esk2_0) = k2_lattices(esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])).

cnf(c_0_24,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k4_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_20]),c_0_21]),c_0_22])]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k2_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = k5_lattices(esk1_0)
    | ~ l1_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_22])]),c_0_16])).

fof(c_0_27,plain,(
    ! [X4] :
      ( ( ~ v2_struct_0(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v4_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v5_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v6_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v7_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v8_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) )
      & ( v9_lattices(X4)
        | v2_struct_0(X4)
        | ~ v10_lattices(X4)
        | ~ l3_lattices(X4) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_28,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r1_lattices(X13,X14,X15)
        | k2_lattices(X13,X14,X15) = X14
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v8_lattices(X13)
        | ~ v9_lattices(X13)
        | ~ l3_lattices(X13) )
      & ( k2_lattices(X13,X14,X15) != X14
        | r1_lattices(X13,X14,X15)
        | ~ m1_subset_1(X15,u1_struct_0(X13))
        | ~ m1_subset_1(X14,u1_struct_0(X13))
        | v2_struct_0(X13)
        | ~ v8_lattices(X13)
        | ~ v9_lattices(X13)
        | ~ l3_lattices(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).

cnf(c_0_29,negated_conjecture,
    ( k2_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = k5_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_22])])).

cnf(c_0_30,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( r1_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | k2_lattices(X1,X2,X3) != X2
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( k2_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) = k5_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_21]),c_0_22])]),c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)
    | ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_15]),c_0_22])]),c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_22])]),c_0_16])).

cnf(c_0_35,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_36,plain,(
    ! [X10,X11,X12] :
      ( ( ~ r3_lattices(X10,X11,X12)
        | r1_lattices(X10,X11,X12)
        | v2_struct_0(X10)
        | ~ v6_lattices(X10)
        | ~ v8_lattices(X10)
        | ~ v9_lattices(X10)
        | ~ l3_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10)) )
      & ( ~ r1_lattices(X10,X11,X12)
        | r3_lattices(X10,X11,X12)
        | v2_struct_0(X10)
        | ~ v6_lattices(X10)
        | ~ v8_lattices(X10)
        | ~ v9_lattices(X10)
        | ~ l3_lattices(X10)
        | ~ m1_subset_1(X11,u1_struct_0(X10))
        | ~ m1_subset_1(X12,u1_struct_0(X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)
    | ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_21]),c_0_22])]),c_0_16])).

cnf(c_0_38,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r3_lattices(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_21]),c_0_22])]),c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( ~ r3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( ~ m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_15]),c_0_22])]),c_0_41]),c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_24]),c_0_22])]),c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_21]),c_0_22])]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( ~ v9_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_35]),c_0_21]),c_0_22])]),c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_21]),c_0_22])]),c_0_16]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.14/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t41_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r3_lattices(X1,k5_lattices(X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattices)).
% 0.14/0.38  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.14/0.38  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.14/0.38  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.14/0.38  fof(t40_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k4_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_lattices)).
% 0.14/0.38  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 0.14/0.38  fof(t21_lattices, axiom, ![X1]:((((~(v2_struct_0(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattices(X1,X2,X3)<=>k2_lattices(X1,X2,X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_lattices)).
% 0.14/0.38  fof(redefinition_r3_lattices, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_lattices(X1,X2,X3)<=>r1_lattices(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 0.14/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r3_lattices(X1,k5_lattices(X1),X2)))), inference(assume_negation,[status(cth)],[t41_lattices])).
% 0.14/0.38  fof(c_0_9, plain, ![X7, X8, X9]:(v2_struct_0(X7)|~v6_lattices(X7)|~l1_lattices(X7)|~m1_subset_1(X8,u1_struct_0(X7))|~m1_subset_1(X9,u1_struct_0(X7))|k4_lattices(X7,X8,X9)=k2_lattices(X7,X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.14/0.38  fof(c_0_10, negated_conjecture, ((((~v2_struct_0(esk1_0)&v10_lattices(esk1_0))&v13_lattices(esk1_0))&l3_lattices(esk1_0))&(m1_subset_1(esk2_0,u1_struct_0(esk1_0))&~r3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X5]:(v2_struct_0(X5)|~l1_lattices(X5)|m1_subset_1(k5_lattices(X5),u1_struct_0(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X6]:((l1_lattices(X6)|~l3_lattices(X6))&(l2_lattices(X6)|~l3_lattices(X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X16, X17]:(v2_struct_0(X16)|~v10_lattices(X16)|~v13_lattices(X16)|~l3_lattices(X16)|(~m1_subset_1(X17,u1_struct_0(X16))|k4_lattices(X16,k5_lattices(X16),X17)=k5_lattices(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t40_lattices])])])])).
% 0.14/0.38  cnf(c_0_14, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk2_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_17, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_18, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_19, plain, (v2_struct_0(X1)|k4_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1)|~v10_lattices(X1)|~v13_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (v13_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (v10_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (l3_lattices(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (k4_lattices(esk1_0,X1,esk2_0)=k2_lattices(esk1_0,X1,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~l1_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])).
% 0.14/0.38  cnf(c_0_24, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (k4_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)=k5_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_15]), c_0_20]), c_0_21]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (k2_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)=k5_lattices(esk1_0)|~l1_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_22])]), c_0_16])).
% 0.14/0.38  fof(c_0_27, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.14/0.38  fof(c_0_28, plain, ![X13, X14, X15]:((~r1_lattices(X13,X14,X15)|k2_lattices(X13,X14,X15)=X14|~m1_subset_1(X15,u1_struct_0(X13))|~m1_subset_1(X14,u1_struct_0(X13))|(v2_struct_0(X13)|~v8_lattices(X13)|~v9_lattices(X13)|~l3_lattices(X13)))&(k2_lattices(X13,X14,X15)!=X14|r1_lattices(X13,X14,X15)|~m1_subset_1(X15,u1_struct_0(X13))|~m1_subset_1(X14,u1_struct_0(X13))|(v2_struct_0(X13)|~v8_lattices(X13)|~v9_lattices(X13)|~l3_lattices(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t21_lattices])])])])])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (k2_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)=k5_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_22])])).
% 0.14/0.38  cnf(c_0_30, plain, (v6_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_31, plain, (r1_lattices(X1,X2,X3)|v2_struct_0(X1)|k2_lattices(X1,X2,X3)!=X2|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (k2_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)=k5_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_21]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)|~m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_15]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_34, negated_conjecture, (r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_24]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_35, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  fof(c_0_36, plain, ![X10, X11, X12]:((~r3_lattices(X10,X11,X12)|r1_lattices(X10,X11,X12)|(v2_struct_0(X10)|~v6_lattices(X10)|~v8_lattices(X10)|~v9_lattices(X10)|~l3_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))))&(~r1_lattices(X10,X11,X12)|r3_lattices(X10,X11,X12)|(v2_struct_0(X10)|~v6_lattices(X10)|~v8_lattices(X10)|~v9_lattices(X10)|~l3_lattices(X10)|~m1_subset_1(X11,u1_struct_0(X10))|~m1_subset_1(X12,u1_struct_0(X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_lattices])])])])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)|~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_21]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_38, plain, (v9_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.38  cnf(c_0_39, plain, (r3_lattices(X1,X2,X3)|v2_struct_0(X1)|~r1_lattices(X1,X2,X3)|~v6_lattices(X1)|~v8_lattices(X1)|~v9_lattices(X1)|~l3_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (r1_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_21]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (~r3_lattices(esk1_0,k5_lattices(esk1_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (~m1_subset_1(k5_lattices(esk1_0),u1_struct_0(esk1_0))|~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_15]), c_0_22])]), c_0_41]), c_0_16])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (~v9_lattices(esk1_0)|~v8_lattices(esk1_0)|~v6_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_24]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (~v9_lattices(esk1_0)|~v8_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_21]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (~v9_lattices(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_35]), c_0_21]), c_0_22])]), c_0_16])).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_21]), c_0_22])]), c_0_16]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 47
% 0.14/0.38  # Proof object clause steps            : 30
% 0.14/0.38  # Proof object formula steps           : 17
% 0.14/0.38  # Proof object conjectures             : 23
% 0.14/0.38  # Proof object clause conjectures      : 20
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 15
% 0.14/0.38  # Proof object initial formulas used   : 8
% 0.14/0.38  # Proof object generating inferences   : 15
% 0.14/0.38  # Proof object simplifying inferences  : 51
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 8
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 22
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 21
% 0.14/0.38  # Processed clauses                    : 66
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 66
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 6
% 0.14/0.38  # Backward-rewritten                   : 4
% 0.14/0.38  # Generated clauses                    : 27
% 0.14/0.38  # ...of the previous two non-trivial   : 25
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 27
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
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
% 0.14/0.38  # Current number of processed clauses  : 35
% 0.14/0.38  #    Positive orientable unit clauses  : 10
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 22
% 0.14/0.38  # Current number of unprocessed clauses: 1
% 0.14/0.38  # ...number of literals in the above   : 1
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 31
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 413
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 96
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.38  # Unit Clause-clause subsumption calls : 1
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 6
% 0.14/0.38  # BW rewrite match successes           : 4
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2807
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.035 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
