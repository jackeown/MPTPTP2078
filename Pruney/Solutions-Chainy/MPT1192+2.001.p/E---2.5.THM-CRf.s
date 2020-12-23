%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:21 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 152 expanded)
%              Number of clauses        :   26 (  51 expanded)
%              Number of leaves         :    7 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  183 ( 810 expanded)
%              Number of equality atoms :   26 ( 107 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_lattices(X1,X2,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(dt_k1_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(redefinition_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(commutativity_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(d8_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v8_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

fof(d9_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l3_lattices(X1) )
     => ( v9_lattices(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v6_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k1_lattices(X1,X2,X2) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t17_lattices])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ l2_lattices(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | m1_subset_1(k1_lattices(X17,X18,X19),u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_lattices])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v6_lattices(esk5_0)
    & v8_lattices(esk5_0)
    & v9_lattices(esk5_0)
    & l3_lattices(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & k1_lattices(esk5_0,esk6_0,esk6_0) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ v6_lattices(X21)
      | ~ l1_lattices(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_subset_1(X23,u1_struct_0(X21))
      | k4_lattices(X21,X22,X23) = k2_lattices(X21,X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).

fof(c_0_11,plain,(
    ! [X4,X5,X6] :
      ( v2_struct_0(X4)
      | ~ v6_lattices(X4)
      | ~ l1_lattices(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | k4_lattices(X4,X5,X6) = k4_lattices(X4,X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k2_lattices(X1,X2,X3)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v6_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | k4_lattices(X1,X2,X3) = k4_lattices(X1,X3,X2)
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v8_lattices(X7)
        | ~ m1_subset_1(X8,u1_struct_0(X7))
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | k1_lattices(X7,k2_lattices(X7,X8,X9),X9) = X9
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( m1_subset_1(esk1_1(X7),u1_struct_0(X7))
        | v8_lattices(X7)
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( m1_subset_1(esk2_1(X7),u1_struct_0(X7))
        | v8_lattices(X7)
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) )
      & ( k1_lattices(X7,k2_lattices(X7,esk1_1(X7),esk2_1(X7)),esk2_1(X7)) != esk2_1(X7)
        | v8_lattices(X7)
        | v2_struct_0(X7)
        | ~ l3_lattices(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(k1_lattices(esk5_0,X1,esk6_0),u1_struct_0(esk5_0))
    | ~ l2_lattices(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( k4_lattices(esk5_0,X1,esk6_0) = k2_lattices(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_16])]),c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( k4_lattices(esk5_0,X1,esk6_0) = k4_lattices(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_16])]),c_0_14])).

cnf(c_0_22,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v8_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( l3_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k4_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk6_0)) = k2_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk6_0))
    | ~ l2_lattices(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_19]),c_0_16])]),c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( k4_lattices(esk5_0,esk6_0,X1) = k2_lattices(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,plain,(
    ! [X12,X13,X14] :
      ( ( ~ v9_lattices(X12)
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | k2_lattices(X12,X13,k1_lattices(X12,X13,X14)) = X13
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk3_1(X12),u1_struct_0(X12))
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( m1_subset_1(esk4_1(X12),u1_struct_0(X12))
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) )
      & ( k2_lattices(X12,esk3_1(X12),k1_lattices(X12,esk3_1(X12),esk4_1(X12))) != esk3_1(X12)
        | v9_lattices(X12)
        | v2_struct_0(X12)
        | ~ l3_lattices(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).

cnf(c_0_28,negated_conjecture,
    ( k1_lattices(esk5_0,k2_lattices(esk5_0,X1,esk6_0),esk6_0) = esk6_0
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_13]),c_0_23]),c_0_24])]),c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( k2_lattices(esk5_0,k1_lattices(esk5_0,X1,esk6_0),esk6_0) = k2_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,X1,esk6_0))
    | ~ l2_lattices(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_13])]),c_0_19])).

cnf(c_0_30,plain,
    ( k2_lattices(X1,X2,k1_lattices(X1,X2,X3)) = X2
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v9_lattices(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( k1_lattices(esk5_0,k2_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,X1,esk6_0)),esk6_0) = esk6_0
    | ~ l2_lattices(esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ l1_lattices(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( k2_lattices(esk5_0,X1,k1_lattices(esk5_0,X1,esk6_0)) = X1
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_13]),c_0_31]),c_0_24])]),c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( k1_lattices(esk5_0,esk6_0,esk6_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_35,plain,(
    ! [X20] :
      ( ( l1_lattices(X20)
        | ~ l3_lattices(X20) )
      & ( l2_lattices(X20)
        | ~ l3_lattices(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_36,negated_conjecture,
    ( ~ l2_lattices(esk5_0)
    | ~ l1_lattices(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_13])]),c_0_34])).

cnf(c_0_37,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( ~ l1_lattices(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_24])])).

cnf(c_0_39,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.043 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t17_lattices, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k1_lattices(X1,X2,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_lattices)).
% 0.20/0.40  fof(dt_k1_lattices, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_lattices)).
% 0.20/0.40  fof(redefinition_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 0.20/0.40  fof(commutativity_k4_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&l1_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 0.20/0.40  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 0.20/0.40  fof(d9_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v9_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattices)).
% 0.20/0.40  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.20/0.40  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v6_lattices(X1))&v8_lattices(X1))&v9_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k1_lattices(X1,X2,X2)=X2))), inference(assume_negation,[status(cth)],[t17_lattices])).
% 0.20/0.40  fof(c_0_8, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~l2_lattices(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|m1_subset_1(k1_lattices(X17,X18,X19),u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_lattices])])])).
% 0.20/0.40  fof(c_0_9, negated_conjecture, (((((~v2_struct_0(esk5_0)&v6_lattices(esk5_0))&v8_lattices(esk5_0))&v9_lattices(esk5_0))&l3_lattices(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&k1_lattices(esk5_0,esk6_0,esk6_0)!=esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.20/0.40  fof(c_0_10, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v6_lattices(X21)|~l1_lattices(X21)|~m1_subset_1(X22,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|k4_lattices(X21,X22,X23)=k2_lattices(X21,X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k4_lattices])])])).
% 0.20/0.40  fof(c_0_11, plain, ![X4, X5, X6]:(v2_struct_0(X4)|~v6_lattices(X4)|~l1_lattices(X4)|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X4))|k4_lattices(X4,X5,X6)=k4_lattices(X4,X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[commutativity_k4_lattices])])])).
% 0.20/0.40  cnf(c_0_12, plain, (v2_struct_0(X1)|m1_subset_1(k1_lattices(X1,X2,X3),u1_struct_0(X1))|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_15, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k2_lattices(X1,X2,X3)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (v6_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_17, plain, (v2_struct_0(X1)|k4_lattices(X1,X2,X3)=k4_lattices(X1,X3,X2)|~v6_lattices(X1)|~l1_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.40  fof(c_0_18, plain, ![X7, X8, X9]:((~v8_lattices(X7)|(~m1_subset_1(X8,u1_struct_0(X7))|(~m1_subset_1(X9,u1_struct_0(X7))|k1_lattices(X7,k2_lattices(X7,X8,X9),X9)=X9))|(v2_struct_0(X7)|~l3_lattices(X7)))&((m1_subset_1(esk1_1(X7),u1_struct_0(X7))|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))&((m1_subset_1(esk2_1(X7),u1_struct_0(X7))|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))&(k1_lattices(X7,k2_lattices(X7,esk1_1(X7),esk2_1(X7)),esk2_1(X7))!=esk2_1(X7)|v8_lattices(X7)|(v2_struct_0(X7)|~l3_lattices(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(k1_lattices(esk5_0,X1,esk6_0),u1_struct_0(esk5_0))|~l2_lattices(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (k4_lattices(esk5_0,X1,esk6_0)=k2_lattices(esk5_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_13]), c_0_16])]), c_0_14])).
% 0.20/0.40  cnf(c_0_21, negated_conjecture, (k4_lattices(esk5_0,X1,esk6_0)=k4_lattices(esk5_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_16])]), c_0_14])).
% 0.20/0.40  cnf(c_0_22, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (v8_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (l3_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (k4_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk6_0))=k2_lattices(esk5_0,X1,k1_lattices(esk5_0,X2,esk6_0))|~l2_lattices(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_19]), c_0_16])]), c_0_14])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (k4_lattices(esk5_0,esk6_0,X1)=k2_lattices(esk5_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.40  fof(c_0_27, plain, ![X12, X13, X14]:((~v9_lattices(X12)|(~m1_subset_1(X13,u1_struct_0(X12))|(~m1_subset_1(X14,u1_struct_0(X12))|k2_lattices(X12,X13,k1_lattices(X12,X13,X14))=X13))|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk3_1(X12),u1_struct_0(X12))|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&((m1_subset_1(esk4_1(X12),u1_struct_0(X12))|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))&(k2_lattices(X12,esk3_1(X12),k1_lattices(X12,esk3_1(X12),esk4_1(X12)))!=esk3_1(X12)|v9_lattices(X12)|(v2_struct_0(X12)|~l3_lattices(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_lattices])])])])])])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (k1_lattices(esk5_0,k2_lattices(esk5_0,X1,esk6_0),esk6_0)=esk6_0|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_13]), c_0_23]), c_0_24])]), c_0_14])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (k2_lattices(esk5_0,k1_lattices(esk5_0,X1,esk6_0),esk6_0)=k2_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,X1,esk6_0))|~l2_lattices(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_13])]), c_0_19])).
% 0.20/0.40  cnf(c_0_30, plain, (k2_lattices(X1,X2,k1_lattices(X1,X2,X3))=X2|v2_struct_0(X1)|~v9_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (v9_lattices(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (k1_lattices(esk5_0,k2_lattices(esk5_0,esk6_0,k1_lattices(esk5_0,X1,esk6_0)),esk6_0)=esk6_0|~l2_lattices(esk5_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~l1_lattices(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (k2_lattices(esk5_0,X1,k1_lattices(esk5_0,X1,esk6_0))=X1|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_13]), c_0_31]), c_0_24])]), c_0_14])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (k1_lattices(esk5_0,esk6_0,esk6_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  fof(c_0_35, plain, ![X20]:((l1_lattices(X20)|~l3_lattices(X20))&(l2_lattices(X20)|~l3_lattices(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (~l2_lattices(esk5_0)|~l1_lattices(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_13])]), c_0_34])).
% 0.20/0.40  cnf(c_0_37, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_38, negated_conjecture, (~l1_lattices(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_24])])).
% 0.20/0.40  cnf(c_0_39, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.40  cnf(c_0_40, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_24])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 41
% 0.20/0.40  # Proof object clause steps            : 26
% 0.20/0.40  # Proof object formula steps           : 15
% 0.20/0.40  # Proof object conjectures             : 22
% 0.20/0.40  # Proof object clause conjectures      : 19
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 14
% 0.20/0.40  # Proof object initial formulas used   : 7
% 0.20/0.40  # Proof object generating inferences   : 12
% 0.20/0.40  # Proof object simplifying inferences  : 29
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 7
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 20
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 20
% 0.20/0.40  # Processed clauses                    : 71
% 0.20/0.40  # ...of these trivial                  : 0
% 0.20/0.40  # ...subsumed                          : 10
% 0.20/0.40  # ...remaining for further processing  : 61
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 5
% 0.20/0.40  # Backward-rewritten                   : 0
% 0.20/0.40  # Generated clauses                    : 77
% 0.20/0.40  # ...of the previous two non-trivial   : 70
% 0.20/0.40  # Contextual simplify-reflections      : 2
% 0.20/0.40  # Paramodulations                      : 77
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 0
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 36
% 0.20/0.40  #    Positive orientable unit clauses  : 5
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 3
% 0.20/0.40  #    Non-unit-clauses                  : 28
% 0.20/0.40  # Current number of unprocessed clauses: 39
% 0.20/0.40  # ...number of literals in the above   : 259
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 25
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 443
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 113
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 17
% 0.20/0.40  # Unit Clause-clause subsumption calls : 29
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 0
% 0.20/0.40  # BW rewrite match successes           : 0
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 5004
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.052 s
% 0.20/0.40  # System time              : 0.004 s
% 0.20/0.40  # Total time               : 0.056 s
% 0.20/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
