%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 135 expanded)
%              Number of clauses        :   27 (  48 expanded)
%              Number of leaves         :    7 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  206 ( 666 expanded)
%              Number of equality atoms :   30 (  90 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t39_lattices,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v13_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(dt_k5_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => m1_subset_1(k5_lattices(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(d16_lattices,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_lattices(X1) )
     => ( v13_lattices(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( X2 = k5_lattices(X1)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( k2_lattices(X1,X2,X3) = X2
                    & k2_lattices(X1,X3,X2) = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(redefinition_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v13_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => k3_lattices(X1,k5_lattices(X1),X2) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t39_lattices])).

fof(c_0_8,plain,(
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

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v10_lattices(esk4_0)
    & v13_lattices(esk4_0)
    & l3_lattices(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & k3_lattices(esk4_0,k5_lattices(esk4_0),esk5_0) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_lattices(X14)
      | m1_subset_1(k5_lattices(X14),u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).

fof(c_0_11,plain,(
    ! [X15] :
      ( ( l1_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( l2_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

fof(c_0_12,plain,(
    ! [X5,X6,X7] :
      ( ( k2_lattices(X5,X6,X7) = X6
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | X6 != k5_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v13_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( k2_lattices(X5,X7,X6) = X6
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | X6 != k5_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v13_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))
        | X6 = k5_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v13_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) )
      & ( k2_lattices(X5,X6,esk1_2(X5,X6)) != X6
        | k2_lattices(X5,esk1_2(X5,X6),X6) != X6
        | X6 = k5_lattices(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ v13_lattices(X5)
        | v2_struct_0(X5)
        | ~ l1_lattices(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).

fof(c_0_13,plain,(
    ! [X16,X17,X18] :
      ( v2_struct_0(X16)
      | ~ v4_lattices(X16)
      | ~ l2_lattices(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | k3_lattices(X16,X17,X18) = k1_lattices(X16,X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).

cnf(c_0_14,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( v10_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( l3_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v8_lattices(X9)
        | ~ m1_subset_1(X10,u1_struct_0(X9))
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | k1_lattices(X9,k2_lattices(X9,X10,X11),X11) = X11
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk2_1(X9),u1_struct_0(X9))
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( m1_subset_1(esk3_1(X9),u1_struct_0(X9))
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) )
      & ( k1_lattices(X9,k2_lattices(X9,esk2_1(X9),esk3_1(X9)),esk3_1(X9)) != esk3_1(X9)
        | v8_lattices(X9)
        | v2_struct_0(X9)
        | ~ l3_lattices(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).

cnf(c_0_21,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( k2_lattices(X1,X2,X3) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | X2 != k5_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | k3_lattices(X1,X2,X3) = k1_lattices(X1,X2,X3)
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v4_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(k5_lattices(X1),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k1_lattices(X1,k2_lattices(X1,X2,X3),X3) = X3
    | v2_struct_0(X1)
    | ~ v8_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v8_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_29,plain,
    ( k2_lattices(X1,k5_lattices(X1),X2) = k5_lattices(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v13_lattices(X1)
    | ~ l1_lattices(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v13_lattices(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( k3_lattices(esk4_0,k5_lattices(esk4_0),esk5_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( k3_lattices(esk4_0,X1,esk5_0) = k1_lattices(esk4_0,X1,esk5_0)
    | ~ l2_lattices(esk4_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k5_lattices(esk4_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( k1_lattices(esk4_0,k2_lattices(esk4_0,X1,esk5_0),esk5_0) = esk5_0
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_28]),c_0_16])]),c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( k2_lattices(esk4_0,k5_lattices(esk4_0),esk5_0) = k5_lattices(esk4_0)
    | ~ l1_lattices(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_30])]),c_0_17])).

cnf(c_0_36,negated_conjecture,
    ( k1_lattices(esk4_0,k5_lattices(esk4_0),esk5_0) != esk5_0
    | ~ l2_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_37,negated_conjecture,
    ( k1_lattices(esk4_0,k5_lattices(esk4_0),esk5_0) = esk5_0
    | ~ l1_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_33])])).

cnf(c_0_38,negated_conjecture,
    ( ~ l2_lattices(esk4_0)
    | ~ l1_lattices(esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_39,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( ~ l1_lattices(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_16])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_19]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.028 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t39_lattices, conjecture, ![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k5_lattices(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_lattices)).
% 0.14/0.37  fof(cc1_lattices, axiom, ![X1]:(l3_lattices(X1)=>((~(v2_struct_0(X1))&v10_lattices(X1))=>((((((~(v2_struct_0(X1))&v4_lattices(X1))&v5_lattices(X1))&v6_lattices(X1))&v7_lattices(X1))&v8_lattices(X1))&v9_lattices(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 0.14/0.37  fof(dt_k5_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>m1_subset_1(k5_lattices(X1),u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_lattices)).
% 0.14/0.37  fof(dt_l3_lattices, axiom, ![X1]:(l3_lattices(X1)=>(l1_lattices(X1)&l2_lattices(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 0.14/0.37  fof(d16_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l1_lattices(X1))=>(v13_lattices(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(X2=k5_lattices(X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(k2_lattices(X1,X2,X3)=X2&k2_lattices(X1,X3,X2)=X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattices)).
% 0.14/0.37  fof(redefinition_k3_lattices, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v4_lattices(X1))&l2_lattices(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 0.14/0.37  fof(d8_lattices, axiom, ![X1]:((~(v2_struct_0(X1))&l3_lattices(X1))=>(v8_lattices(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 0.14/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v10_lattices(X1))&v13_lattices(X1))&l3_lattices(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k3_lattices(X1,k5_lattices(X1),X2)=X2))), inference(assume_negation,[status(cth)],[t39_lattices])).
% 0.14/0.37  fof(c_0_8, plain, ![X4]:(((((((~v2_struct_0(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))&(v4_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v5_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v6_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v7_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v8_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4)))&(v9_lattices(X4)|(v2_struct_0(X4)|~v10_lattices(X4))|~l3_lattices(X4))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).
% 0.14/0.37  fof(c_0_9, negated_conjecture, ((((~v2_struct_0(esk4_0)&v10_lattices(esk4_0))&v13_lattices(esk4_0))&l3_lattices(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&k3_lattices(esk4_0,k5_lattices(esk4_0),esk5_0)!=esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.14/0.37  fof(c_0_10, plain, ![X14]:(v2_struct_0(X14)|~l1_lattices(X14)|m1_subset_1(k5_lattices(X14),u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_lattices])])])).
% 0.14/0.37  fof(c_0_11, plain, ![X15]:((l1_lattices(X15)|~l3_lattices(X15))&(l2_lattices(X15)|~l3_lattices(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).
% 0.14/0.37  fof(c_0_12, plain, ![X5, X6, X7]:(((k2_lattices(X5,X6,X7)=X6|~m1_subset_1(X7,u1_struct_0(X5))|X6!=k5_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~v13_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5)))&(k2_lattices(X5,X7,X6)=X6|~m1_subset_1(X7,u1_struct_0(X5))|X6!=k5_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~v13_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5))))&((m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))|X6=k5_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~v13_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5)))&(k2_lattices(X5,X6,esk1_2(X5,X6))!=X6|k2_lattices(X5,esk1_2(X5,X6),X6)!=X6|X6=k5_lattices(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~v13_lattices(X5)|(v2_struct_0(X5)|~l1_lattices(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_lattices])])])])])])).
% 0.14/0.37  fof(c_0_13, plain, ![X16, X17, X18]:(v2_struct_0(X16)|~v4_lattices(X16)|~l2_lattices(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|k3_lattices(X16,X17,X18)=k1_lattices(X16,X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_lattices])])])).
% 0.14/0.37  cnf(c_0_14, plain, (v4_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_15, negated_conjecture, (v10_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_16, negated_conjecture, (l3_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_18, plain, (v2_struct_0(X1)|m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_19, plain, (l1_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  fof(c_0_20, plain, ![X9, X10, X11]:((~v8_lattices(X9)|(~m1_subset_1(X10,u1_struct_0(X9))|(~m1_subset_1(X11,u1_struct_0(X9))|k1_lattices(X9,k2_lattices(X9,X10,X11),X11)=X11))|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk2_1(X9),u1_struct_0(X9))|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&((m1_subset_1(esk3_1(X9),u1_struct_0(X9))|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))&(k1_lattices(X9,k2_lattices(X9,esk2_1(X9),esk3_1(X9)),esk3_1(X9))!=esk3_1(X9)|v8_lattices(X9)|(v2_struct_0(X9)|~l3_lattices(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_lattices])])])])])])).
% 0.14/0.37  cnf(c_0_21, plain, (v8_lattices(X1)|v2_struct_0(X1)|~v10_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_22, plain, (k2_lattices(X1,X2,X3)=X2|v2_struct_0(X1)|~m1_subset_1(X3,u1_struct_0(X1))|X2!=k5_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.37  cnf(c_0_23, plain, (v2_struct_0(X1)|k3_lattices(X1,X2,X3)=k1_lattices(X1,X2,X3)|~v4_lattices(X1)|~l2_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (v4_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])]), c_0_17])).
% 0.14/0.37  cnf(c_0_26, plain, (m1_subset_1(k5_lattices(X1),u1_struct_0(X1))|v2_struct_0(X1)|~l3_lattices(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.37  cnf(c_0_27, plain, (k1_lattices(X1,k2_lattices(X1,X2,X3),X3)=X3|v2_struct_0(X1)|~v8_lattices(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (v8_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_15]), c_0_16])]), c_0_17])).
% 0.14/0.37  cnf(c_0_29, plain, (k2_lattices(X1,k5_lattices(X1),X2)=k5_lattices(X1)|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v13_lattices(X1)|~l1_lattices(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_18])).
% 0.14/0.37  cnf(c_0_30, negated_conjecture, (v13_lattices(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_31, negated_conjecture, (k3_lattices(esk4_0,k5_lattices(esk4_0),esk5_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_32, negated_conjecture, (k3_lattices(esk4_0,X1,esk5_0)=k1_lattices(esk4_0,X1,esk5_0)|~l2_lattices(esk4_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])]), c_0_17])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (m1_subset_1(k5_lattices(esk4_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_17])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (k1_lattices(esk4_0,k2_lattices(esk4_0,X1,esk5_0),esk5_0)=esk5_0|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_24]), c_0_28]), c_0_16])]), c_0_17])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (k2_lattices(esk4_0,k5_lattices(esk4_0),esk5_0)=k5_lattices(esk4_0)|~l1_lattices(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_30])]), c_0_17])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (k1_lattices(esk4_0,k5_lattices(esk4_0),esk5_0)!=esk5_0|~l2_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, (k1_lattices(esk4_0,k5_lattices(esk4_0),esk5_0)=esk5_0|~l1_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_33])])).
% 0.14/0.37  cnf(c_0_38, negated_conjecture, (~l2_lattices(esk4_0)|~l1_lattices(esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.37  cnf(c_0_39, plain, (l2_lattices(X1)|~l3_lattices(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (~l1_lattices(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_16])])).
% 0.14/0.37  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_19]), c_0_16])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 42
% 0.14/0.37  # Proof object clause steps            : 27
% 0.14/0.37  # Proof object formula steps           : 15
% 0.14/0.37  # Proof object conjectures             : 20
% 0.14/0.37  # Proof object clause conjectures      : 17
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 14
% 0.14/0.37  # Proof object initial formulas used   : 7
% 0.14/0.37  # Proof object generating inferences   : 12
% 0.14/0.37  # Proof object simplifying inferences  : 27
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 7
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 25
% 0.14/0.37  # Removed in clause preprocessing      : 1
% 0.14/0.37  # Initial clauses in saturation        : 24
% 0.14/0.37  # Processed clauses                    : 76
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 1
% 0.14/0.37  # ...remaining for further processing  : 75
% 0.14/0.37  # Other redundant clauses eliminated   : 2
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 4
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 40
% 0.14/0.37  # ...of the previous two non-trivial   : 37
% 0.14/0.37  # Contextual simplify-reflections      : 2
% 0.14/0.37  # Paramodulations                      : 38
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 2
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 45
% 0.14/0.37  #    Positive orientable unit clauses  : 11
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 3
% 0.14/0.37  #    Non-unit-clauses                  : 31
% 0.14/0.37  # Current number of unprocessed clauses: 9
% 0.14/0.37  # ...number of literals in the above   : 38
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 28
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 351
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 171
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.14/0.37  # Unit Clause-clause subsumption calls : 8
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 3020
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.033 s
% 0.14/0.37  # System time              : 0.002 s
% 0.14/0.37  # Total time               : 0.035 s
% 0.14/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
