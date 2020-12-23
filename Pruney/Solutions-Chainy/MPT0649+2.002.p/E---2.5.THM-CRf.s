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
% DateTime   : Thu Dec  3 10:53:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 351 expanded)
%              Number of clauses        :   29 ( 127 expanded)
%              Number of leaves         :    8 (  85 expanded)
%              Depth                    :    8
%              Number of atoms          :  191 (1561 expanded)
%              Number of equality atoms :   30 ( 403 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t56_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(c_0_8,plain,(
    ! [X22,X23,X24] :
      ( ( r2_hidden(X22,k1_relat_1(X24))
        | ~ r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( X23 = k1_funct_1(X24,X22)
        | ~ r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( ~ r2_hidden(X22,k1_relat_1(X24))
        | X23 != k1_funct_1(X24,X22)
        | r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k1_relat_1(X2)) )
         => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
            & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_funct_1])).

fof(c_0_10,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(k4_tarski(X7,X8),X6)
        | r2_hidden(k4_tarski(X8,X7),X5)
        | X6 != k4_relat_1(X5)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X10,X9),X5)
        | r2_hidden(k4_tarski(X9,X10),X6)
        | X6 != k4_relat_1(X5)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r2_hidden(k4_tarski(esk2_2(X5,X6),esk1_2(X5,X6)),X5)
        | X6 = k4_relat_1(X5)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) )
      & ( r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | r2_hidden(k4_tarski(esk2_2(X5,X6),esk1_2(X5,X6)),X5)
        | X6 = k4_relat_1(X5)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | v1_relat_1(k4_relat_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_12,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & v2_funct_1(esk4_0)
    & r2_hidden(esk3_0,k1_relat_1(esk4_0))
    & ( esk3_0 != k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk3_0))
      | esk3_0 != k1_funct_1(k5_relat_1(esk4_0,k2_funct_1(esk4_0)),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X15] :
      ( ( v1_relat_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( v1_funct_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_15,plain,(
    ! [X14] :
      ( ~ v1_relat_1(X14)
      | ~ v1_funct_1(X14)
      | ~ v2_funct_1(X14)
      | k2_funct_1(X14) = k4_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_25,plain,(
    ! [X16,X17,X18] :
      ( ( r2_hidden(X16,k1_relat_1(X18))
        | ~ r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(k1_funct_1(X18,X16),k1_relat_1(X17))
        | ~ r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X16,k1_relat_1(X18))
        | ~ r2_hidden(k1_funct_1(X18,X16),k1_relat_1(X17))
        | r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X2,X1),X3)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]),c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk4_0,esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21])])).

cnf(c_0_29,negated_conjecture,
    ( k2_funct_1(esk4_0) = k4_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_20]),c_0_24]),c_0_21])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk4_0,esk3_0),esk3_0),k4_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 != k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk3_0))
    | esk3_0 != k1_funct_1(k5_relat_1(esk4_0,k2_funct_1(esk4_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_37,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ r2_hidden(X19,k1_relat_1(k5_relat_1(X21,X20)))
      | k1_funct_1(k5_relat_1(X21,X20),X19) = k1_funct_1(X20,k1_funct_1(X21,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk4_0,X1)))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(k1_funct_1(esk4_0,esk3_0),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,esk3_0),k1_relat_1(k4_relat_1(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(k4_relat_1(esk4_0),k1_funct_1(esk4_0,esk3_0)) != esk3_0
    | k1_funct_1(k5_relat_1(esk4_0,k4_relat_1(esk4_0)),esk3_0) != esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_29]),c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(k4_relat_1(esk4_0),k1_funct_1(esk4_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_42,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk4_0,k4_relat_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_33]),c_0_34])])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk4_0,k4_relat_1(esk4_0)),esk3_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_41]),c_0_20]),c_0_33]),c_0_21]),c_0_34])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.13/0.38  # and selection function SelectGrCQArEqFirst.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.13/0.38  fof(t56_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 0.13/0.38  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 0.13/0.38  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.13/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.38  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.13/0.38  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 0.13/0.38  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.13/0.38  fof(c_0_8, plain, ![X22, X23, X24]:(((r2_hidden(X22,k1_relat_1(X24))|~r2_hidden(k4_tarski(X22,X23),X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(X23=k1_funct_1(X24,X22)|~r2_hidden(k4_tarski(X22,X23),X24)|(~v1_relat_1(X24)|~v1_funct_1(X24))))&(~r2_hidden(X22,k1_relat_1(X24))|X23!=k1_funct_1(X24,X22)|r2_hidden(k4_tarski(X22,X23),X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1))))), inference(assume_negation,[status(cth)],[t56_funct_1])).
% 0.13/0.38  fof(c_0_10, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(k4_tarski(X7,X8),X6)|r2_hidden(k4_tarski(X8,X7),X5)|X6!=k4_relat_1(X5)|~v1_relat_1(X6)|~v1_relat_1(X5))&(~r2_hidden(k4_tarski(X10,X9),X5)|r2_hidden(k4_tarski(X9,X10),X6)|X6!=k4_relat_1(X5)|~v1_relat_1(X6)|~v1_relat_1(X5)))&((~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|~r2_hidden(k4_tarski(esk2_2(X5,X6),esk1_2(X5,X6)),X5)|X6=k4_relat_1(X5)|~v1_relat_1(X6)|~v1_relat_1(X5))&(r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|r2_hidden(k4_tarski(esk2_2(X5,X6),esk1_2(X5,X6)),X5)|X6=k4_relat_1(X5)|~v1_relat_1(X6)|~v1_relat_1(X5)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X13]:(~v1_relat_1(X13)|v1_relat_1(k4_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.13/0.38  cnf(c_0_12, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&((v2_funct_1(esk4_0)&r2_hidden(esk3_0,k1_relat_1(esk4_0)))&(esk3_0!=k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk3_0))|esk3_0!=k1_funct_1(k5_relat_1(esk4_0,k2_funct_1(esk4_0)),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X15]:((v1_relat_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(v1_funct_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X14]:(~v1_relat_1(X14)|~v1_funct_1(X14)|(~v2_funct_1(X14)|k2_funct_1(X14)=k4_relat_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.13/0.38  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k4_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_17, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_18, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_22, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_23, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_25, plain, ![X16, X17, X18]:(((r2_hidden(X16,k1_relat_1(X18))|~r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))|(~v1_relat_1(X18)|~v1_funct_1(X18))|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(r2_hidden(k1_funct_1(X18,X16),k1_relat_1(X17))|~r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))|(~v1_relat_1(X18)|~v1_funct_1(X18))|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(X16,k1_relat_1(X18))|~r2_hidden(k1_funct_1(X18,X16),k1_relat_1(X17))|r2_hidden(X16,k1_relat_1(k5_relat_1(X18,X17)))|(~v1_relat_1(X18)|~v1_funct_1(X18))|(~v1_relat_1(X17)|~v1_funct_1(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.13/0.38  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))|~r2_hidden(k4_tarski(X2,X1),X3)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_16]), c_0_17])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk4_0,esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (k2_funct_1(esk4_0)=k4_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_20]), c_0_24]), c_0_21])])).
% 0.13/0.38  cnf(c_0_30, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_31, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk4_0,esk3_0),esk3_0),k4_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_21])])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_1(k4_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v1_relat_1(k4_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_17, c_0_21])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (esk3_0!=k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk3_0))|esk3_0!=k1_funct_1(k5_relat_1(esk4_0,k2_funct_1(esk4_0)),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_36, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  fof(c_0_37, plain, ![X19, X20, X21]:(~v1_relat_1(X20)|~v1_funct_1(X20)|(~v1_relat_1(X21)|~v1_funct_1(X21)|(~r2_hidden(X19,k1_relat_1(k5_relat_1(X21,X20)))|k1_funct_1(k5_relat_1(X21,X20),X19)=k1_funct_1(X20,k1_funct_1(X21,X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk4_0,X1)))|~v1_funct_1(X1)|~r2_hidden(k1_funct_1(esk4_0,esk3_0),k1_relat_1(X1))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_19]), c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,esk3_0),k1_relat_1(k4_relat_1(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k1_funct_1(k4_relat_1(esk4_0),k1_funct_1(esk4_0,esk3_0))!=esk3_0|k1_funct_1(k5_relat_1(esk4_0,k4_relat_1(esk4_0)),esk3_0)!=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_29]), c_0_29])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k1_funct_1(k4_relat_1(esk4_0),k1_funct_1(esk4_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_32]), c_0_33]), c_0_34])])).
% 0.13/0.38  cnf(c_0_42, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(k5_relat_1(esk4_0,k4_relat_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_33]), c_0_34])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k1_funct_1(k5_relat_1(esk4_0,k4_relat_1(esk4_0)),esk3_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_41]), c_0_20]), c_0_33]), c_0_21]), c_0_34])]), c_0_44]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 46
% 0.13/0.38  # Proof object clause steps            : 29
% 0.13/0.38  # Proof object formula steps           : 17
% 0.13/0.38  # Proof object conjectures             : 21
% 0.13/0.38  # Proof object clause conjectures      : 18
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 8
% 0.13/0.38  # Proof object generating inferences   : 10
% 0.13/0.38  # Proof object simplifying inferences  : 37
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 8
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 20
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 20
% 0.13/0.38  # Processed clauses                    : 82
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 79
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 6
% 0.13/0.38  # Generated clauses                    : 82
% 0.13/0.38  # ...of the previous two non-trivial   : 82
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 79
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 50
% 0.13/0.38  #    Positive orientable unit clauses  : 32
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 17
% 0.13/0.38  # Current number of unprocessed clauses: 32
% 0.13/0.38  # ...number of literals in the above   : 92
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 26
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 309
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 52
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 73
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 37
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3991
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
