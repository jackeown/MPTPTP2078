%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0548+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  73 expanded)
%              Number of clauses        :   17 (  38 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 219 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t150_relat_1,conjecture,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(c_0_5,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X12,X13,X14,X15,X17] :
      ( ( r2_hidden(k4_tarski(esk1_4(X7,X8,X9,X10),X10),X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k9_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk1_4(X7,X8,X9,X10),X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k9_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(X13,X12),X7)
        | ~ r2_hidden(X13,X8)
        | r2_hidden(X12,X9)
        | X9 != k9_relat_1(X7,X8)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(esk2_3(X7,X14,X15),X15)
        | ~ r2_hidden(k4_tarski(X17,esk2_3(X7,X14,X15)),X7)
        | ~ r2_hidden(X17,X14)
        | X15 = k9_relat_1(X7,X14)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk3_3(X7,X14,X15),esk2_3(X7,X14,X15)),X7)
        | r2_hidden(esk2_3(X7,X14,X15),X15)
        | X15 = k9_relat_1(X7,X14)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(esk3_3(X7,X14,X15),X14)
        | r2_hidden(esk2_3(X7,X14,X15),X15)
        | X15 = k9_relat_1(X7,X14)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( X1 = k9_relat_1(X2,X3)
    | r2_hidden(esk3_3(X2,X3,X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_10,plain,
    ( X1 = k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_xboole_0(X3)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_9])).

cnf(c_0_11,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_12,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | v1_relat_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_13,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),esk2_3(X1,X2,X3)),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_17,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11])).

cnf(c_0_18,plain,
    ( X1 = k9_relat_1(X2,X3)
    | r2_hidden(esk2_3(X2,X3,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_15]),c_0_14])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t150_relat_1])).

cnf(c_0_20,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( X1 = k9_relat_1(X2,X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_7,c_0_18])).

fof(c_0_22,negated_conjecture,(
    k9_relat_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_23,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_20]),c_0_11])])).

cnf(c_0_24,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,esk4_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_25,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])]),
    [proof]).

%------------------------------------------------------------------------------
