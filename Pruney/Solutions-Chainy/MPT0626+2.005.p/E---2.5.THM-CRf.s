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
% DateTime   : Thu Dec  3 10:53:16 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 (4920 expanded)
%              Number of clauses        :   66 (1774 expanded)
%              Number of leaves         :    6 (1189 expanded)
%              Depth                    :   38
%              Number of atoms          :  315 (32353 expanded)
%              Number of equality atoms :   48 (1943 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   38 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t21_funct_1,conjecture,(
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

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(d8_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( X3 = k5_relat_1(X1,X2)
              <=> ! [X4,X5] :
                    ( r2_hidden(k4_tarski(X4,X5),X3)
                  <=> ? [X6] :
                        ( r2_hidden(k4_tarski(X4,X6),X1)
                        & r2_hidden(k4_tarski(X6,X5),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_6,plain,(
    ! [X22,X23,X24] :
      ( ( X24 != k1_funct_1(X22,X23)
        | r2_hidden(k4_tarski(X23,X24),X22)
        | ~ r2_hidden(X23,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X24 = k1_funct_1(X22,X23)
        | ~ r2_hidden(X23,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X24 != k1_funct_1(X22,X23)
        | X24 = k1_xboole_0
        | r2_hidden(X23,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X24 != k1_xboole_0
        | X24 = k1_funct_1(X22,X23)
        | r2_hidden(X23,k1_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
            <=> ( r2_hidden(X1,k1_relat_1(X3))
                & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_funct_1])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & ( ~ r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
      | ~ r2_hidden(esk5_0,k1_relat_1(esk7_0))
      | ~ r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0)) )
    & ( r2_hidden(esk5_0,k1_relat_1(esk7_0))
      | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) )
    & ( r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))
      | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk7_0))
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X25,X26] :
      ( ( v1_relat_1(k5_relat_1(X25,X26))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( v1_funct_1(k5_relat_1(X25,X26))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11,X13,X14,X15,X18] :
      ( ( r2_hidden(k4_tarski(X10,esk1_5(X7,X8,X9,X10,X11)),X7)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_5(X7,X8,X9,X10,X11),X11),X8)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X13,X15),X7)
        | ~ r2_hidden(k4_tarski(X15,X14),X8)
        | r2_hidden(k4_tarski(X13,X14),X9)
        | X9 != k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)
        | ~ r2_hidden(k4_tarski(esk2_3(X7,X8,X9),X18),X7)
        | ~ r2_hidden(k4_tarski(X18,esk3_3(X7,X8,X9)),X8)
        | X9 = k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk4_3(X7,X8,X9)),X7)
        | r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)
        | X9 = k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk4_3(X7,X8,X9),esk3_3(X7,X8,X9)),X8)
        | r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)
        | X9 = k5_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).

fof(c_0_14,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_relat_1(X21)
      | v1_relat_1(k5_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))
    | r2_hidden(esk5_0,k1_relat_1(esk7_0))
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)
    | ~ r2_hidden(k4_tarski(X1,X5),X4)
    | X4 != k5_relat_1(X2,X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))
    | r2_hidden(esk5_0,k1_relat_1(esk7_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_25,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X28 = k1_funct_1(X29,X27)
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X27,k1_relat_1(X29))
        | X28 != k1_funct_1(X29,X27)
        | r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,esk1_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)
    | ~ r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))
    | r2_hidden(esk5_0,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_19]),c_0_20])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X4),X6)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X2,X4),X5)
    | X6 != k5_relat_1(X3,X5)
    | ~ v1_relat_1(X6)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_19])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))),esk7_0)
    | r2_hidden(esk5_0,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_19]),c_0_20])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))
    | ~ r2_hidden(k4_tarski(X5,X2),X4)
    | ~ r2_hidden(k4_tarski(X1,X5),X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,k1_funct_1(esk6_0,X1)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_30]),c_0_17]),c_0_19])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_18]),c_0_20])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,k1_funct_1(esk6_0,X1)),k5_relat_1(X3,esk6_0))
    | ~ r2_hidden(k4_tarski(X2,X1),X3)
    | ~ v1_relat_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_19])])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk7_0,esk5_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_35]),c_0_18]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0)) = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))),k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_20])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0)) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | ~ r2_hidden(esk5_0,k1_relat_1(esk7_0))
    | ~ r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0)) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | ~ r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0)) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_23]),c_0_19]),c_0_20])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))),esk6_0)
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_42]),c_0_17]),c_0_19])])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk5_0),k1_xboole_0),esk6_0)
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | r2_hidden(k4_tarski(X1,k1_xboole_0),k5_relat_1(X2,esk6_0))
    | ~ r2_hidden(k4_tarski(X1,k1_funct_1(esk7_0,esk5_0)),X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_47]),c_0_19])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_37]),c_0_20])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))
    | r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))
    | r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))
    | r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_23]),c_0_19]),c_0_20])])).

cnf(c_0_53,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))),esk7_0)
    | r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_52]),c_0_19]),c_0_20])])).

cnf(c_0_55,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0)
    | r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_18]),c_0_20])])).

cnf(c_0_56,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0)
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0)
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_58,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0)
    | r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_23]),c_0_19]),c_0_20])])).

cnf(c_0_59,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0)
    | r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0)
    | r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_61,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0)
    | r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_23]),c_0_19]),c_0_20])])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)
    | ~ r2_hidden(k4_tarski(X4,X5),X3)
    | X3 != k5_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0)
    | r2_hidden(k4_tarski(esk5_0,esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_61]),c_0_19]),c_0_20])])).

cnf(c_0_64,plain,
    ( r2_hidden(k4_tarski(esk1_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)
    | ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_62]),c_0_23])).

cnf(c_0_65,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)) = k1_funct_1(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_63]),c_0_18]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk5_0),k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),esk6_0)
    | r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_52]),c_0_19]),c_0_20])]),c_0_65])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))
    | ~ r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_49])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_66]),c_0_17]),c_0_19])]),c_0_67])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0) = k1_xboole_0
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0) = k1_xboole_0
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_23]),c_0_19]),c_0_20])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_74,negated_conjecture,
    ( esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_xboole_0) = k1_funct_1(esk7_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_23]),c_0_19]),c_0_20])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk5_0),k1_xboole_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_68]),c_0_19]),c_0_20])]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_75])])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_76]),c_0_17]),c_0_19])]),c_0_77]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.47  # and selection function SelectNewComplexAHP.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.027 s
% 0.20/0.47  # Presaturation interreduction done
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.20/0.47  fof(t21_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 0.20/0.47  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.20/0.47  fof(d8_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k5_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>?[X6]:(r2_hidden(k4_tarski(X4,X6),X1)&r2_hidden(k4_tarski(X6,X5),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 0.20/0.47  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.20/0.47  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.47  fof(c_0_6, plain, ![X22, X23, X24]:(((X24!=k1_funct_1(X22,X23)|r2_hidden(k4_tarski(X23,X24),X22)|~r2_hidden(X23,k1_relat_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(~r2_hidden(k4_tarski(X23,X24),X22)|X24=k1_funct_1(X22,X23)|~r2_hidden(X23,k1_relat_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22))))&((X24!=k1_funct_1(X22,X23)|X24=k1_xboole_0|r2_hidden(X23,k1_relat_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(X24!=k1_xboole_0|X24=k1_funct_1(X22,X23)|r2_hidden(X23,k1_relat_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.20/0.47  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t21_funct_1])).
% 0.20/0.47  cnf(c_0_8, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((~r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|(~r2_hidden(esk5_0,k1_relat_1(esk7_0))|~r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))))&((r2_hidden(esk5_0,k1_relat_1(esk7_0))|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0))))&(r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.20/0.47  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_8])).
% 0.20/0.47  cnf(c_0_11, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk7_0))|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  fof(c_0_12, plain, ![X25, X26]:((v1_relat_1(k5_relat_1(X25,X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)|~v1_relat_1(X26)|~v1_funct_1(X26)))&(v1_funct_1(k5_relat_1(X25,X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)|~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.20/0.47  fof(c_0_13, plain, ![X7, X8, X9, X10, X11, X13, X14, X15, X18]:((((r2_hidden(k4_tarski(X10,esk1_5(X7,X8,X9,X10,X11)),X7)|~r2_hidden(k4_tarski(X10,X11),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk1_5(X7,X8,X9,X10,X11),X11),X8)|~r2_hidden(k4_tarski(X10,X11),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7)))&(~r2_hidden(k4_tarski(X13,X15),X7)|~r2_hidden(k4_tarski(X15,X14),X8)|r2_hidden(k4_tarski(X13,X14),X9)|X9!=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7)))&((~r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|(~r2_hidden(k4_tarski(esk2_3(X7,X8,X9),X18),X7)|~r2_hidden(k4_tarski(X18,esk3_3(X7,X8,X9)),X8))|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&((r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk4_3(X7,X8,X9)),X7)|r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))&(r2_hidden(k4_tarski(esk4_3(X7,X8,X9),esk3_3(X7,X8,X9)),X8)|r2_hidden(k4_tarski(esk2_3(X7,X8,X9),esk3_3(X7,X8,X9)),X9)|X9=k5_relat_1(X7,X8)|~v1_relat_1(X9)|~v1_relat_1(X8)|~v1_relat_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_1])])])])])])).
% 0.20/0.47  fof(c_0_14, plain, ![X20, X21]:(~v1_relat_1(X20)|~v1_relat_1(X21)|v1_relat_1(k5_relat_1(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.20/0.47  cnf(c_0_15, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))|r2_hidden(esk5_0,k1_relat_1(esk7_0))|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.47  cnf(c_0_16, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_funct_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.47  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,esk1_5(X2,X3,X4,X1,X5)),X2)|~r2_hidden(k4_tarski(X1,X5),X4)|X4!=k5_relat_1(X2,X3)|~v1_relat_1(X4)|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_23, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.47  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))|r2_hidden(esk5_0,k1_relat_1(esk7_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_25, plain, (k1_funct_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.47  fof(c_0_26, plain, ![X27, X28, X29]:(((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X28=k1_funct_1(X29,X27)|~r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(~r2_hidden(X27,k1_relat_1(X29))|X28!=k1_funct_1(X29,X27)|r2_hidden(k4_tarski(X27,X28),X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.47  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,esk1_5(X2,X3,k5_relat_1(X2,X3),X1,X4)),X2)|~r2_hidden(k4_tarski(X1,X4),k5_relat_1(X2,X3))|~v1_relat_1(X3)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_22]), c_0_23])).
% 0.20/0.47  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))|r2_hidden(esk5_0,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X1,X4),X6)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X2,X4),X5)|X6!=k5_relat_1(X3,X5)|~v1_relat_1(X6)|~v1_relat_1(X5)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk6_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_19])])).
% 0.20/0.47  cnf(c_0_31, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))),esk7_0)|r2_hidden(esk5_0,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,X4))|~r2_hidden(k4_tarski(X5,X2),X4)|~r2_hidden(k4_tarski(X1,X5),X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_23])).
% 0.20/0.47  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk6_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,k1_funct_1(esk6_0,X1)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_30]), c_0_17]), c_0_19])])).
% 0.20/0.47  cnf(c_0_35, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_18]), c_0_20])])).
% 0.20/0.47  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk6_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X2,k1_funct_1(esk6_0,X1)),k5_relat_1(X3,esk6_0))|~r2_hidden(k4_tarski(X2,X1),X3)|~v1_relat_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_19])])).
% 0.20/0.47  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk7_0,esk5_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_35]), c_0_18]), c_0_20])])).
% 0.20/0.47  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))=k1_xboole_0|r2_hidden(k4_tarski(esk5_0,k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))),k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_20])])).
% 0.20/0.47  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))=k1_xboole_0|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_31, c_0_38])).
% 0.20/0.47  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|~r2_hidden(esk5_0,k1_relat_1(esk7_0))|~r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))=k1_xboole_0|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.47  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|~r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_35])])).
% 0.20/0.47  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))=k1_xboole_0|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_23]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk5_0),k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))),esk6_0)|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_42]), c_0_17]), c_0_19])])).
% 0.20/0.47  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(esk7_0,esk5_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_30])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk5_0),k1_xboole_0),esk6_0)|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.47  cnf(c_0_48, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|r2_hidden(k4_tarski(X1,k1_xboole_0),k5_relat_1(X2,esk6_0))|~r2_hidden(k4_tarski(X1,k1_funct_1(esk7_0,esk5_0)),X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_47]), c_0_19])])).
% 0.20/0.47  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_37]), c_0_20])])).
% 0.20/0.47  cnf(c_0_50, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))|r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_10, c_0_49])).
% 0.20/0.47  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))|r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_52, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))|r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_23]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_53, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_54, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))),esk7_0)|r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_52]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)|r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_18]), c_0_20])])).
% 0.20/0.47  cnf(c_0_56, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_31, c_0_55])).
% 0.20/0.47  cnf(c_0_57, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_58, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)|r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_23]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_59, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)|r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_10, c_0_58])).
% 0.20/0.47  cnf(c_0_60, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)|r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)|r2_hidden(k4_tarski(esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_23]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_62, plain, (r2_hidden(k4_tarski(esk1_5(X1,X2,X3,X4,X5),X5),X2)|~r2_hidden(k4_tarski(X4,X5),X3)|X3!=k5_relat_1(X1,X2)|~v1_relat_1(X3)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_63, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)|r2_hidden(k4_tarski(esk5_0,esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_61]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_64, plain, (r2_hidden(k4_tarski(esk1_5(X1,X2,k5_relat_1(X1,X2),X3,X4),X4),X2)|~r2_hidden(k4_tarski(X3,X4),k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_62]), c_0_23])).
% 0.20/0.47  cnf(c_0_65, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0))=k1_funct_1(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_63]), c_0_18]), c_0_20])])).
% 0.20/0.47  cnf(c_0_66, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk5_0),k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)),esk6_0)|r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_52]), c_0_19]), c_0_20])]), c_0_65])).
% 0.20/0.47  cnf(c_0_67, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))|~r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_49])).
% 0.20/0.47  cnf(c_0_68, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,k1_xboole_0),k5_relat_1(esk7_0,esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_66]), c_0_17]), c_0_19])]), c_0_67])).
% 0.20/0.47  cnf(c_0_69, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)=k1_xboole_0|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_53, c_0_68])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)=k1_xboole_0|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_71, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(spm,[status(thm)],[c_0_31, c_0_68])).
% 0.20/0.47  cnf(c_0_72, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_23]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_73, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_74, negated_conjecture, (esk1_5(esk7_0,esk6_0,k5_relat_1(esk7_0,esk6_0),esk5_0,k1_xboole_0)=k1_funct_1(esk7_0,esk5_0)), inference(rw,[status(thm)],[c_0_65, c_0_72])).
% 0.20/0.47  cnf(c_0_75, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(k5_relat_1(esk7_0,esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_23]), c_0_19]), c_0_20])])).
% 0.20/0.47  cnf(c_0_76, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk5_0),k1_xboole_0),esk6_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_68]), c_0_19]), c_0_20])]), c_0_74])).
% 0.20/0.47  cnf(c_0_77, negated_conjecture, (~r2_hidden(k1_funct_1(esk7_0,esk5_0),k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_75])])).
% 0.20/0.47  cnf(c_0_78, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_76]), c_0_17]), c_0_19])]), c_0_77]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 79
% 0.20/0.47  # Proof object clause steps            : 66
% 0.20/0.47  # Proof object formula steps           : 13
% 0.20/0.47  # Proof object conjectures             : 55
% 0.20/0.47  # Proof object clause conjectures      : 52
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 16
% 0.20/0.47  # Proof object initial formulas used   : 6
% 0.20/0.47  # Proof object generating inferences   : 41
% 0.20/0.47  # Proof object simplifying inferences  : 124
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 6
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 23
% 0.20/0.47  # Removed in clause preprocessing      : 0
% 0.20/0.47  # Initial clauses in saturation        : 23
% 0.20/0.47  # Processed clauses                    : 557
% 0.20/0.47  # ...of these trivial                  : 6
% 0.20/0.47  # ...subsumed                          : 66
% 0.20/0.47  # ...remaining for further processing  : 485
% 0.20/0.47  # Other redundant clauses eliminated   : 7
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 194
% 0.20/0.47  # Backward-rewritten                   : 110
% 0.20/0.47  # Generated clauses                    : 1295
% 0.20/0.47  # ...of the previous two non-trivial   : 1286
% 0.20/0.47  # Contextual simplify-reflections      : 23
% 0.20/0.47  # Paramodulations                      : 1283
% 0.20/0.47  # Factorizations                       : 5
% 0.20/0.47  # Equation resolutions                 : 7
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 155
% 0.20/0.47  #    Positive orientable unit clauses  : 12
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 1
% 0.20/0.47  #    Non-unit-clauses                  : 142
% 0.20/0.47  # Current number of unprocessed clauses: 755
% 0.20/0.47  # ...number of literals in the above   : 4029
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 323
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 16929
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 3327
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 273
% 0.20/0.47  # Unit Clause-clause subsumption calls : 162
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 12
% 0.20/0.47  # BW rewrite match successes           : 6
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 49255
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.114 s
% 0.20/0.47  # System time              : 0.008 s
% 0.20/0.47  # Total time               : 0.122 s
% 0.20/0.47  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
