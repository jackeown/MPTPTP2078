%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0538+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:46 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 (  68 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t138_relat_1,conjecture,(
    ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X11,X7)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k8_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(X10,X11),X8)
        | ~ r2_hidden(k4_tarski(X10,X11),X9)
        | X9 != k8_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(X13,X7)
        | ~ r2_hidden(k4_tarski(X12,X13),X8)
        | r2_hidden(k4_tarski(X12,X13),X9)
        | X9 != k8_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( ~ r2_hidden(k4_tarski(esk1_3(X7,X8,X9),esk2_3(X7,X8,X9)),X9)
        | ~ r2_hidden(esk2_3(X7,X8,X9),X7)
        | ~ r2_hidden(k4_tarski(esk1_3(X7,X8,X9),esk2_3(X7,X8,X9)),X8)
        | X9 = k8_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(esk2_3(X7,X8,X9),X7)
        | r2_hidden(k4_tarski(esk1_3(X7,X8,X9),esk2_3(X7,X8,X9)),X9)
        | X9 = k8_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) )
      & ( r2_hidden(k4_tarski(esk1_3(X7,X8,X9),esk2_3(X7,X8,X9)),X8)
        | r2_hidden(k4_tarski(esk1_3(X7,X8,X9),esk2_3(X7,X8,X9)),X9)
        | X9 = k8_relat_1(X7,X8)
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X21,X22] :
      ( ~ r2_hidden(X21,X22)
      | ~ v1_xboole_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_7,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X2)
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X3),esk2_3(X1,X2,X3)),X3)
    | X3 = k8_relat_1(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] : k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t138_relat_1])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k8_relat_1(X1,X2) = X2
    | r2_hidden(k4_tarski(esk1_3(X1,X2,X2),esk2_3(X1,X2,X2)),X2)
    | ~ v1_relat_1(X2) ),
    inference(ef,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
    k8_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( k8_relat_1(X1,X2) = X2
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])).

cnf(c_0_15,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_16,negated_conjecture,
    ( k8_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k8_relat_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17])]),
    [proof]).

%------------------------------------------------------------------------------
