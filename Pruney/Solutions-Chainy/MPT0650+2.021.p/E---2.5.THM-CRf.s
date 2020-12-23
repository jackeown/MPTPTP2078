%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:48 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 203 expanded)
%              Number of clauses        :   30 (  76 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  213 (1011 expanded)
%              Number of equality atoms :   34 ( 249 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_9,plain,(
    ! [X26,X27,X28] :
      ( ( r2_hidden(X26,k1_relat_1(X28))
        | ~ r2_hidden(k4_tarski(X26,X27),X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( X27 = k1_funct_1(X28,X26)
        | ~ r2_hidden(k4_tarski(X26,X27),X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( ~ r2_hidden(X26,k1_relat_1(X28))
        | X27 != k1_funct_1(X28,X26)
        | r2_hidden(k4_tarski(X26,X27),X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v2_funct_1(esk5_0)
    & r2_hidden(esk4_0,k2_relat_1(esk5_0))
    & ( esk4_0 != k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))
      | esk4_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_11,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X19] :
      ( ( v1_relat_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( v1_funct_1(k2_funct_1(X19))
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_13,negated_conjecture,
    ( esk4_0 != k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))
    | esk4_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( X1 = X2
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(k4_tarski(X4,X2),X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_11])).

fof(c_0_15,plain,(
    ! [X20,X21,X22] :
      ( ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ r2_hidden(X20,k1_relat_1(X21))
      | k1_funct_1(k5_relat_1(X21,X22),X20) = k1_funct_1(X22,k1_funct_1(X21,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) != esk4_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14])])).

cnf(c_0_20,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_22,plain,(
    ! [X23] :
      ( ( k2_relat_1(X23) = k1_relat_1(k2_funct_1(X23))
        | ~ v2_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( k1_relat_1(X23) = k2_relat_1(k2_funct_1(X23))
        | ~ v2_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_23,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)
        | X6 != k2_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X10,X9),X5)
        | r2_hidden(X9,X6)
        | X6 != k2_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)
        | X12 = k2_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)
        | X12 = k2_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(esk4_0,k1_relat_1(k2_funct_1(esk5_0)))
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_17]),c_0_18]),c_0_21])]),c_0_14])).

cnf(c_0_25,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_28,plain,(
    ! [X16,X17,X18] :
      ( ( r2_hidden(X16,k1_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(X17,k2_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X16,X17),X18)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_17]),c_0_18])])).

cnf(c_0_31,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_17]),c_0_18])])).

fof(c_0_35,plain,(
    ! [X24,X25] :
      ( ( X24 = k1_funct_1(k2_funct_1(X25),k1_funct_1(X25,X24))
        | ~ v2_funct_1(X25)
        | ~ r2_hidden(X24,k1_relat_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( X24 = k1_funct_1(k5_relat_1(X25,k2_funct_1(X25)),X24)
        | ~ v2_funct_1(X25)
        | ~ r2_hidden(X24,k1_relat_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),X4))),X1)
    | ~ r2_hidden(k4_tarski(X5,esk4_0),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ r2_hidden(k4_tarski(X5,X4),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_14])).

cnf(c_0_39,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_18])])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,k1_funct_1(esk5_0,X4)),X1)
    | ~ r2_hidden(k4_tarski(X5,k1_funct_1(esk5_0,X4)),X2)
    | ~ r2_hidden(k4_tarski(X5,esk4_0),X2)
    | ~ r2_hidden(X4,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_27]),c_0_17]),c_0_18])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0),k1_funct_1(esk5_0,esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_17]),c_0_18])])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0))),X1)
    | ~ r2_hidden(k4_tarski(X2,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_17]),c_0_18]),c_0_41])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0),esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_17]),c_0_18])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_33]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.61/0.78  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.61/0.78  # and selection function PSelectUnlessUniqMaxPos.
% 0.61/0.78  #
% 0.61/0.78  # Preprocessing time       : 0.028 s
% 0.61/0.78  # Presaturation interreduction done
% 0.61/0.78  
% 0.61/0.78  # Proof found!
% 0.61/0.78  # SZS status Theorem
% 0.61/0.78  # SZS output start CNFRefutation
% 0.61/0.78  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 0.61/0.78  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.61/0.78  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.61/0.78  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 0.61/0.78  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.61/0.78  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.61/0.78  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 0.61/0.78  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 0.61/0.78  fof(c_0_8, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 0.61/0.78  fof(c_0_9, plain, ![X26, X27, X28]:(((r2_hidden(X26,k1_relat_1(X28))|~r2_hidden(k4_tarski(X26,X27),X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(X27=k1_funct_1(X28,X26)|~r2_hidden(k4_tarski(X26,X27),X28)|(~v1_relat_1(X28)|~v1_funct_1(X28))))&(~r2_hidden(X26,k1_relat_1(X28))|X27!=k1_funct_1(X28,X26)|r2_hidden(k4_tarski(X26,X27),X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.61/0.78  fof(c_0_10, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v2_funct_1(esk5_0)&r2_hidden(esk4_0,k2_relat_1(esk5_0)))&(esk4_0!=k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))|esk4_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.61/0.78  cnf(c_0_11, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.61/0.78  fof(c_0_12, plain, ![X19]:((v1_relat_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(v1_funct_1(k2_funct_1(X19))|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.61/0.78  cnf(c_0_13, negated_conjecture, (esk4_0!=k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))|esk4_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.61/0.78  cnf(c_0_14, plain, (X1=X2|~v1_funct_1(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(k4_tarski(X4,X2),X3)), inference(spm,[status(thm)],[c_0_11, c_0_11])).
% 0.61/0.78  fof(c_0_15, plain, ![X20, X21, X22]:(~v1_relat_1(X21)|~v1_funct_1(X21)|(~v1_relat_1(X22)|~v1_funct_1(X22)|(~r2_hidden(X20,k1_relat_1(X21))|k1_funct_1(k5_relat_1(X21,X22),X20)=k1_funct_1(X22,k1_funct_1(X21,X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.61/0.78  cnf(c_0_16, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.61/0.78  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.61/0.78  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.61/0.78  cnf(c_0_19, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)!=esk4_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14])])).
% 0.61/0.78  cnf(c_0_20, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.61/0.78  cnf(c_0_21, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.61/0.78  fof(c_0_22, plain, ![X23]:((k2_relat_1(X23)=k1_relat_1(k2_funct_1(X23))|~v2_funct_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(k1_relat_1(X23)=k2_relat_1(k2_funct_1(X23))|~v2_funct_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.61/0.78  fof(c_0_23, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)|X6!=k2_relat_1(X5))&(~r2_hidden(k4_tarski(X10,X9),X5)|r2_hidden(X9,X6)|X6!=k2_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.61/0.78  cnf(c_0_24, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)|~r2_hidden(esk4_0,k1_relat_1(k2_funct_1(esk5_0)))|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_17]), c_0_18]), c_0_21])]), c_0_14])).
% 0.61/0.78  cnf(c_0_25, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.61/0.78  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.61/0.78  cnf(c_0_27, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.61/0.78  fof(c_0_28, plain, ![X16, X17, X18]:((r2_hidden(X16,k1_relat_1(X18))|~r2_hidden(k4_tarski(X16,X17),X18)|~v1_relat_1(X18))&(r2_hidden(X17,k2_relat_1(X18))|~r2_hidden(k4_tarski(X16,X17),X18)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.61/0.78  cnf(c_0_29, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.61/0.78  cnf(c_0_30, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_17]), c_0_18])])).
% 0.61/0.78  cnf(c_0_31, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.61/0.78  cnf(c_0_32, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.61/0.78  cnf(c_0_33, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_29])).
% 0.61/0.78  cnf(c_0_34, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),X1)|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_17]), c_0_18])])).
% 0.61/0.78  fof(c_0_35, plain, ![X24, X25]:((X24=k1_funct_1(k2_funct_1(X25),k1_funct_1(X25,X24))|(~v2_funct_1(X25)|~r2_hidden(X24,k1_relat_1(X25)))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(X24=k1_funct_1(k5_relat_1(X25,k2_funct_1(X25)),X24)|(~v2_funct_1(X25)|~r2_hidden(X24,k1_relat_1(X25)))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.61/0.78  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.61/0.78  cnf(c_0_37, plain, (r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.61/0.78  cnf(c_0_38, negated_conjecture, (~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),X4))),X1)|~r2_hidden(k4_tarski(X5,esk4_0),X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~r2_hidden(k4_tarski(X5,X4),X2)), inference(spm,[status(thm)],[c_0_34, c_0_14])).
% 0.61/0.78  cnf(c_0_39, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.61/0.78  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_36])).
% 0.61/0.78  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_18])])).
% 0.61/0.78  cnf(c_0_42, negated_conjecture, (~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,k1_funct_1(esk5_0,X4)),X1)|~r2_hidden(k4_tarski(X5,k1_funct_1(esk5_0,X4)),X2)|~r2_hidden(k4_tarski(X5,esk4_0),X2)|~r2_hidden(X4,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_27]), c_0_17]), c_0_18])])).
% 0.61/0.78  cnf(c_0_43, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0),k1_funct_1(esk5_0,esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0))),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_17]), c_0_18])])).
% 0.61/0.78  cnf(c_0_44, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk5_0,esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0))),X1)|~r2_hidden(k4_tarski(X2,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_17]), c_0_18]), c_0_41])])).
% 0.61/0.78  cnf(c_0_45, negated_conjecture, (~r2_hidden(k4_tarski(esk1_3(esk5_0,k2_relat_1(esk5_0),esk4_0),esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_17]), c_0_18])])).
% 0.61/0.78  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_33]), c_0_26])]), ['proof']).
% 0.61/0.78  # SZS output end CNFRefutation
% 0.61/0.78  # Proof object total steps             : 47
% 0.61/0.78  # Proof object clause steps            : 30
% 0.61/0.78  # Proof object formula steps           : 17
% 0.61/0.78  # Proof object conjectures             : 20
% 0.61/0.78  # Proof object clause conjectures      : 17
% 0.61/0.78  # Proof object formula conjectures     : 3
% 0.61/0.78  # Proof object initial clauses used    : 14
% 0.61/0.78  # Proof object initial formulas used   : 8
% 0.61/0.78  # Proof object generating inferences   : 14
% 0.61/0.78  # Proof object simplifying inferences  : 36
% 0.61/0.78  # Training examples: 0 positive, 0 negative
% 0.61/0.78  # Parsed axioms                        : 8
% 0.61/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.78  # Initial clauses                      : 21
% 0.61/0.78  # Removed in clause preprocessing      : 0
% 0.61/0.78  # Initial clauses in saturation        : 21
% 0.61/0.78  # Processed clauses                    : 560
% 0.61/0.78  # ...of these trivial                  : 0
% 0.61/0.78  # ...subsumed                          : 83
% 0.61/0.78  # ...remaining for further processing  : 477
% 0.61/0.78  # Other redundant clauses eliminated   : 609
% 0.61/0.78  # Clauses deleted for lack of memory   : 0
% 0.61/0.78  # Backward-subsumed                    : 35
% 0.61/0.78  # Backward-rewritten                   : 0
% 0.61/0.78  # Generated clauses                    : 30865
% 0.61/0.78  # ...of the previous two non-trivial   : 30233
% 0.61/0.78  # Contextual simplify-reflections      : 33
% 0.61/0.78  # Paramodulations                      : 30254
% 0.61/0.78  # Factorizations                       : 2
% 0.61/0.78  # Equation resolutions                 : 609
% 0.61/0.78  # Propositional unsat checks           : 0
% 0.61/0.78  #    Propositional check models        : 0
% 0.61/0.78  #    Propositional check unsatisfiable : 0
% 0.61/0.78  #    Propositional clauses             : 0
% 0.61/0.78  #    Propositional clauses after purity: 0
% 0.61/0.78  #    Propositional unsat core size     : 0
% 0.61/0.78  #    Propositional preprocessing time  : 0.000
% 0.61/0.78  #    Propositional encoding time       : 0.000
% 0.61/0.78  #    Propositional solver time         : 0.000
% 0.61/0.78  #    Success case prop preproc time    : 0.000
% 0.61/0.78  #    Success case prop encoding time   : 0.000
% 0.61/0.78  #    Success case prop solver time     : 0.000
% 0.61/0.78  # Current number of processed clauses  : 420
% 0.61/0.78  #    Positive orientable unit clauses  : 38
% 0.61/0.78  #    Positive unorientable unit clauses: 0
% 0.61/0.78  #    Negative unit clauses             : 1
% 0.61/0.78  #    Non-unit-clauses                  : 381
% 0.61/0.78  # Current number of unprocessed clauses: 29652
% 0.61/0.78  # ...number of literals in the above   : 227893
% 0.61/0.78  # Current number of archived formulas  : 0
% 0.61/0.78  # Current number of archived clauses   : 54
% 0.61/0.78  # Clause-clause subsumption calls (NU) : 14584
% 0.61/0.78  # Rec. Clause-clause subsumption calls : 3620
% 0.61/0.78  # Non-unit clause-clause subsumptions  : 151
% 0.61/0.78  # Unit Clause-clause subsumption calls : 144
% 0.61/0.78  # Rewrite failures with RHS unbound    : 0
% 0.61/0.78  # BW rewrite match attempts            : 930
% 0.61/0.78  # BW rewrite match successes           : 0
% 0.61/0.78  # Condensation attempts                : 0
% 0.61/0.78  # Condensation successes               : 0
% 0.61/0.78  # Termbank termtop insertions          : 1019812
% 0.61/0.79  
% 0.61/0.79  # -------------------------------------------------
% 0.61/0.79  # User time                : 0.415 s
% 0.61/0.79  # System time              : 0.030 s
% 0.61/0.79  # Total time               : 0.445 s
% 0.61/0.79  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
