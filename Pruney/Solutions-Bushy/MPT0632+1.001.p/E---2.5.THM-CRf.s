%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0632+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:56 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (1142 expanded)
%              Number of clauses        :   38 ( 439 expanded)
%              Number of leaves         :    6 ( 270 expanded)
%              Depth                    :   12
%              Number of atoms          :  216 (7912 expanded)
%              Number of equality atoms :   94 (3805 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(t34_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(c_0_6,plain,(
    ! [X18,X19,X20] :
      ( ( r2_hidden(X18,k1_relat_1(X20))
        | ~ r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X19 = k1_funct_1(X20,X18)
        | ~ r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(X18,k1_relat_1(X20))
        | X19 != k1_funct_1(X20,X18)
        | r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_7,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X5)
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( X7 = X8
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X9,X5)
        | X9 != X10
        | r2_hidden(k4_tarski(X9,X10),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r2_hidden(esk1_2(X5,X6),X5)
        | esk1_2(X5,X6) != esk2_2(X5,X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( esk1_2(X5,X6) = esk2_2(X5,X6)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( X2 = k6_relat_1(X1)
        <=> ( k1_relat_1(X2) = X1
            & ! [X3] :
                ( r2_hidden(X3,X1)
               => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_funct_1])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( esk1_2(X1,X2) = esk2_2(X1,X2)
    | r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | X2 = k6_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,(
    ! [X24] :
      ( v1_relat_1(esk4_0)
      & v1_funct_1(esk4_0)
      & ( r2_hidden(esk5_0,esk3_0)
        | k1_relat_1(esk4_0) != esk3_0
        | esk4_0 != k6_relat_1(esk3_0) )
      & ( k1_funct_1(esk4_0,esk5_0) != esk5_0
        | k1_relat_1(esk4_0) != esk3_0
        | esk4_0 != k6_relat_1(esk3_0) )
      & ( k1_relat_1(esk4_0) = esk3_0
        | esk4_0 = k6_relat_1(esk3_0) )
      & ( ~ r2_hidden(X24,esk3_0)
        | k1_funct_1(esk4_0,X24) = X24
        | esk4_0 = k6_relat_1(esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

cnf(c_0_13,plain,
    ( X1 = k6_relat_1(X2)
    | r2_hidden(esk1_2(X2,X1),k1_relat_1(X1))
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( esk1_2(X1,X2) = esk2_2(X1,X2)
    | X2 = k6_relat_1(X1)
    | r2_hidden(esk1_2(X1,X2),k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0
    | esk4_0 = k6_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X13,X14,X15] :
      ( ( X15 != k1_funct_1(X13,X14)
        | r2_hidden(k4_tarski(X14,X15),X13)
        | ~ r2_hidden(X14,k1_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),X13)
        | X15 = k1_funct_1(X13,X14)
        | ~ r2_hidden(X14,k1_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X15 != k1_funct_1(X13,X14)
        | X15 = k1_xboole_0
        | r2_hidden(X14,k1_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X15 != k1_xboole_0
        | X15 = k1_funct_1(X13,X14)
        | r2_hidden(X14,k1_relat_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

cnf(c_0_19,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | r2_hidden(esk1_2(k1_relat_1(X1),X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(ef,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | esk4_0 = k6_relat_1(esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( esk1_2(X1,esk4_0) = esk2_2(X1,esk4_0)
    | k6_relat_1(esk3_0) = esk4_0
    | k6_relat_1(X1) = esk4_0
    | r2_hidden(esk1_2(X1,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | r2_hidden(esk1_2(esk3_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(X1,esk4_0)) = esk1_2(X1,esk4_0)
    | esk1_2(X1,esk4_0) = esk2_2(X1,esk4_0)
    | k6_relat_1(esk3_0) = esk4_0
    | k6_relat_1(X1) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( k1_funct_1(X1,esk1_2(X2,X1)) = esk2_2(X2,X1)
    | esk1_2(X2,X1) = esk2_2(X2,X1)
    | X1 = k6_relat_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_2(esk3_0,esk4_0)) = esk1_2(esk3_0,esk4_0)
    | k6_relat_1(esk3_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_24])).

cnf(c_0_29,plain,
    ( X2 = k6_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | esk1_2(X1,X2) != esk2_2(X1,X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( esk1_2(X1,esk4_0) = esk2_2(X1,esk4_0)
    | k6_relat_1(esk3_0) = esk4_0
    | k6_relat_1(X1) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_16]),c_0_17])])).

cnf(c_0_31,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk3_0,esk4_0)),esk4_0)
    | ~ r2_hidden(esk1_2(esk3_0,esk4_0),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_16]),c_0_17])])).

cnf(c_0_32,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | k6_relat_1(X1) = esk4_0
    | ~ r2_hidden(k4_tarski(esk2_2(X1,esk4_0),esk2_2(X1,esk4_0)),esk4_0)
    | ~ r2_hidden(esk2_2(X1,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17])])).

cnf(c_0_33,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | r2_hidden(esk2_2(esk3_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

fof(c_0_34,plain,(
    ! [X16] : v1_relat_1(k6_relat_1(X16)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_35,plain,(
    ! [X17] :
      ( k1_relat_1(k6_relat_1(X17)) = X17
      & k2_relat_1(k6_relat_1(X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_36,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | r2_hidden(k4_tarski(esk1_2(esk3_0,esk4_0),esk1_2(esk3_0,esk4_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_15]),c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0
    | ~ r2_hidden(k4_tarski(esk2_2(esk3_0,esk4_0),esk2_2(esk3_0,esk4_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k6_relat_1(esk3_0) = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_37])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_39])])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) != esk5_0
    | k1_relat_1(esk4_0) != esk3_0
    | esk4_0 != k6_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( k1_funct_1(k6_relat_1(X1),X2) = X2
    | ~ v1_funct_1(k6_relat_1(X1))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_40]),c_0_39])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | k1_relat_1(esk4_0) != esk3_0
    | esk4_0 != k6_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_41])]),c_0_44])])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk4_0,X1) = X1
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_16])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_41])]),c_0_44])])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])]),
    [proof]).

%------------------------------------------------------------------------------
