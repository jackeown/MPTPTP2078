%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:41 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 209 expanded)
%              Number of clauses        :   31 (  68 expanded)
%              Number of leaves         :    7 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  197 (1523 expanded)
%              Number of equality atoms :   64 ( 603 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( ( k1_relat_1(X2) = X1
              & k1_relat_1(X3) = X1
              & r1_tarski(k2_relat_1(X3),X1)
              & v2_funct_1(X2)
              & k5_relat_1(X3,X2) = X2 )
           => X3 = k6_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(t123_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X1,X2) = k5_relat_1(X2,k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(t40_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_1)).

fof(t125_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k8_relat_1(X1,X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( ( k1_relat_1(X2) = X1
                & k1_relat_1(X3) = X1
                & r1_tarski(k2_relat_1(X3),X1)
                & v2_funct_1(X2)
                & k5_relat_1(X3,X2) = X2 )
             => X3 = k6_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_funct_1])).

fof(c_0_8,plain,(
    ! [X16,X17,X18] :
      ( ( k1_relat_1(X17) = X16
        | X17 != k6_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X18,X16)
        | k1_funct_1(X17,X18) = X18
        | X17 != k6_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk3_2(X16,X17),X16)
        | k1_relat_1(X17) != X16
        | X17 = k6_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_funct_1(X17,esk3_2(X16,X17)) != esk3_2(X16,X17)
        | k1_relat_1(X17) != X16
        | X17 = k6_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X5)
      | k8_relat_1(X4,X5) = k5_relat_1(X5,k6_relat_1(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & k1_relat_1(esk5_0) = esk4_0
    & k1_relat_1(esk6_0) = esk4_0
    & r1_tarski(k2_relat_1(esk6_0),esk4_0)
    & v2_funct_1(esk5_0)
    & k5_relat_1(esk6_0,esk5_0) = esk5_0
    & esk6_0 != k6_relat_1(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_funct_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(X8))
        | ~ r2_hidden(X10,k1_relat_1(X8))
        | k1_funct_1(X8,X9) != k1_funct_1(X8,X10)
        | X9 = X10
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk1_1(X8),k1_relat_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk2_1(X8),k1_relat_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( k1_funct_1(X8,esk1_1(X8)) = k1_funct_1(X8,esk2_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( esk1_1(X8) != esk2_1(X8)
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X2 = k6_relat_1(X1)
    | k1_relat_1(X2) != X1
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X20,X21,X22] :
      ( ( r2_hidden(X20,k1_relat_1(X22))
        | ~ r2_hidden(X20,k1_relat_1(k5_relat_1(X22,k6_relat_1(X21))))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(k1_funct_1(X22,X20),X21)
        | ~ r2_hidden(X20,k1_relat_1(k5_relat_1(X22,k6_relat_1(X21))))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(X20,k1_relat_1(X22))
        | ~ r2_hidden(k1_funct_1(X22,X20),X21)
        | r2_hidden(X20,k1_relat_1(k5_relat_1(X22,k6_relat_1(X21))))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).

cnf(c_0_14,plain,
    ( k8_relat_1(X2,X1) = k5_relat_1(X1,k6_relat_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X7)
      | ~ r1_tarski(k2_relat_1(X7),X6)
      | k8_relat_1(X6,X7) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).

cnf(c_0_17,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk3_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 != k6_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( k5_relat_1(esk6_0,k6_relat_1(X1)) = k8_relat_1(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_28,plain,
    ( k8_relat_1(X2,X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_30,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))
      | k1_funct_1(k5_relat_1(X15,X14),X13) = k1_funct_1(X14,k1_funct_1(X15,X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_31,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,X2)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_2(esk4_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_15])]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),X2)
    | ~ r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_23]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( k8_relat_1(esk4_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_15])])).

cnf(c_0_35,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k5_relat_1(esk6_0,esk5_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,plain,
    ( X1 = k6_relat_1(X2)
    | k1_funct_1(X1,esk3_2(X2,X1)) != esk3_2(X2,X1)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,negated_conjecture,
    ( X1 = esk3_2(esk4_0,esk6_0)
    | k1_funct_1(esk5_0,X1) != k1_funct_1(esk5_0,esk3_2(esk4_0,esk6_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1)) = k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_19]),c_0_23]),c_0_20]),c_0_15]),c_0_21])])).

cnf(c_0_41,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k1_funct_1(X1,esk3_2(k1_relat_1(X1),X1)) != esk3_2(k1_relat_1(X1),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk3_2(esk4_0,esk6_0)
    | k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1)) != k1_funct_1(esk5_0,esk3_2(esk4_0,esk6_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(esk6_0,esk3_2(esk4_0,esk6_0))) = k1_funct_1(esk5_0,esk3_2(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_2(esk4_0,esk6_0)) != esk3_2(esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_24]),c_0_24]),c_0_24]),c_0_15])]),c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_32]),c_0_43])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:20:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04AI
% 0.12/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.037 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t50_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_1)).
% 0.12/0.39  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 0.12/0.39  fof(t123_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k8_relat_1(X1,X2)=k5_relat_1(X2,k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 0.12/0.39  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.12/0.39  fof(t40_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_1)).
% 0.12/0.39  fof(t125_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k8_relat_1(X1,X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 0.12/0.39  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 0.12/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(((((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)&r1_tarski(k2_relat_1(X3),X1))&v2_funct_1(X2))&k5_relat_1(X3,X2)=X2)=>X3=k6_relat_1(X1))))), inference(assume_negation,[status(cth)],[t50_funct_1])).
% 0.12/0.39  fof(c_0_8, plain, ![X16, X17, X18]:(((k1_relat_1(X17)=X16|X17!=k6_relat_1(X16)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(~r2_hidden(X18,X16)|k1_funct_1(X17,X18)=X18|X17!=k6_relat_1(X16)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&((r2_hidden(esk3_2(X16,X17),X16)|k1_relat_1(X17)!=X16|X17=k6_relat_1(X16)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(k1_funct_1(X17,esk3_2(X16,X17))!=esk3_2(X16,X17)|k1_relat_1(X17)!=X16|X17=k6_relat_1(X16)|(~v1_relat_1(X17)|~v1_funct_1(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.12/0.39  fof(c_0_9, plain, ![X4, X5]:(~v1_relat_1(X5)|k8_relat_1(X4,X5)=k5_relat_1(X5,k6_relat_1(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t123_relat_1])])).
% 0.12/0.39  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(((((k1_relat_1(esk5_0)=esk4_0&k1_relat_1(esk6_0)=esk4_0)&r1_tarski(k2_relat_1(esk6_0),esk4_0))&v2_funct_1(esk5_0))&k5_relat_1(esk6_0,esk5_0)=esk5_0)&esk6_0!=k6_relat_1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.39  fof(c_0_11, plain, ![X8, X9, X10]:((~v2_funct_1(X8)|(~r2_hidden(X9,k1_relat_1(X8))|~r2_hidden(X10,k1_relat_1(X8))|k1_funct_1(X8,X9)!=k1_funct_1(X8,X10)|X9=X10)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&((((r2_hidden(esk1_1(X8),k1_relat_1(X8))|v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(r2_hidden(esk2_1(X8),k1_relat_1(X8))|v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(k1_funct_1(X8,esk1_1(X8))=k1_funct_1(X8,esk2_1(X8))|v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))&(esk1_1(X8)!=esk2_1(X8)|v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.12/0.39  cnf(c_0_12, plain, (r2_hidden(esk3_2(X1,X2),X1)|X2=k6_relat_1(X1)|k1_relat_1(X2)!=X1|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  fof(c_0_13, plain, ![X20, X21, X22]:(((r2_hidden(X20,k1_relat_1(X22))|~r2_hidden(X20,k1_relat_1(k5_relat_1(X22,k6_relat_1(X21))))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(r2_hidden(k1_funct_1(X22,X20),X21)|~r2_hidden(X20,k1_relat_1(k5_relat_1(X22,k6_relat_1(X21))))|(~v1_relat_1(X22)|~v1_funct_1(X22))))&(~r2_hidden(X20,k1_relat_1(X22))|~r2_hidden(k1_funct_1(X22,X20),X21)|r2_hidden(X20,k1_relat_1(k5_relat_1(X22,k6_relat_1(X21))))|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).
% 0.12/0.39  cnf(c_0_14, plain, (k8_relat_1(X2,X1)=k5_relat_1(X1,k6_relat_1(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  fof(c_0_16, plain, ![X6, X7]:(~v1_relat_1(X7)|(~r1_tarski(k2_relat_1(X7),X6)|k8_relat_1(X6,X7)=X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t125_relat_1])])).
% 0.12/0.39  cnf(c_0_17, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_18, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_19, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_22, plain, (k6_relat_1(k1_relat_1(X1))=X1|r2_hidden(esk3_2(k1_relat_1(X1),X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_25, negated_conjecture, (esk6_0!=k6_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_26, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,k6_relat_1(X3))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (k5_relat_1(esk6_0,k6_relat_1(X1))=k8_relat_1(X1,esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.39  cnf(c_0_28, plain, (k8_relat_1(X2,X1)=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_29, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  fof(c_0_30, plain, ![X13, X14, X15]:(~v1_relat_1(X14)|~v1_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15)|(~r2_hidden(X13,k1_relat_1(k5_relat_1(X15,X14)))|k1_funct_1(k5_relat_1(X15,X14),X13)=k1_funct_1(X14,k1_funct_1(X15,X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (X1=X2|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,X2)|~r2_hidden(X2,esk4_0)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_19]), c_0_20]), c_0_21])])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_2(esk4_0,esk6_0),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_15])]), c_0_25])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),X2)|~r2_hidden(X1,k1_relat_1(k8_relat_1(X2,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_23]), c_0_15])])).
% 0.12/0.39  cnf(c_0_34, negated_conjecture, (k8_relat_1(esk4_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_15])])).
% 0.12/0.39  cnf(c_0_35, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (k5_relat_1(esk6_0,esk5_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.39  cnf(c_0_37, plain, (X1=k6_relat_1(X2)|k1_funct_1(X1,esk3_2(X2,X1))!=esk3_2(X2,X1)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_38, negated_conjecture, (X1=esk3_2(esk4_0,esk6_0)|k1_funct_1(esk5_0,X1)!=k1_funct_1(esk5_0,esk3_2(esk4_0,esk6_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),esk4_0)|~r2_hidden(X1,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_24])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1))=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_19]), c_0_23]), c_0_20]), c_0_15]), c_0_21])])).
% 0.12/0.39  cnf(c_0_41, plain, (k6_relat_1(k1_relat_1(X1))=X1|k1_funct_1(X1,esk3_2(k1_relat_1(X1),X1))!=esk3_2(k1_relat_1(X1),X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_37])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk3_2(esk4_0,esk6_0)|k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1))!=k1_funct_1(esk5_0,esk3_2(esk4_0,esk6_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(esk6_0,esk3_2(esk4_0,esk6_0)))=k1_funct_1(esk5_0,esk3_2(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_40, c_0_32])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk6_0,esk3_2(esk4_0,esk6_0))!=esk3_2(esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_23]), c_0_24]), c_0_24]), c_0_24]), c_0_15])]), c_0_25])).
% 0.12/0.39  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_32]), c_0_43])]), c_0_44]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 46
% 0.12/0.39  # Proof object clause steps            : 31
% 0.12/0.39  # Proof object formula steps           : 15
% 0.12/0.39  # Proof object conjectures             : 25
% 0.12/0.39  # Proof object clause conjectures      : 22
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 17
% 0.12/0.39  # Proof object initial formulas used   : 7
% 0.12/0.39  # Proof object generating inferences   : 12
% 0.12/0.39  # Proof object simplifying inferences  : 34
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 7
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 25
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 25
% 0.12/0.39  # Processed clauses                    : 76
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 0
% 0.12/0.39  # ...remaining for further processing  : 76
% 0.12/0.39  # Other redundant clauses eliminated   : 4
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 0
% 0.12/0.39  # Backward-rewritten                   : 0
% 0.12/0.39  # Generated clauses                    : 51
% 0.12/0.39  # ...of the previous two non-trivial   : 42
% 0.12/0.39  # Contextual simplify-reflections      : 0
% 0.12/0.39  # Paramodulations                      : 47
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 4
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 47
% 0.12/0.39  #    Positive orientable unit clauses  : 14
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 2
% 0.12/0.39  #    Non-unit-clauses                  : 31
% 0.12/0.39  # Current number of unprocessed clauses: 16
% 0.12/0.39  # ...number of literals in the above   : 69
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 25
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 192
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 67
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.39  # Unit Clause-clause subsumption calls : 5
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 0
% 0.12/0.39  # BW rewrite match successes           : 0
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 3135
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.046 s
% 0.12/0.39  # System time              : 0.002 s
% 0.12/0.39  # Total time               : 0.048 s
% 0.12/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
