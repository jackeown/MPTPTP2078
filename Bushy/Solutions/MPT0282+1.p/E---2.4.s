%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t83_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:12 EDT 2019

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 136 expanded)
%              Number of clauses        :   27 (  67 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 476 expanded)
%              Number of equality atoms :   24 ( 132 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_zfmisc_1,conjecture,(
    ! [X1,X2] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',t83_zfmisc_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',t17_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',d1_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',d4_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',t1_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t83_zfmisc_1.p',t19_xboole_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] : k1_zfmisc_1(k3_xboole_0(X1,X2)) = k3_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ),
    inference(assume_negation,[status(cth)],[t83_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X28,X29] : r1_tarski(k3_xboole_0(X28,X29),X28) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_9,plain,(
    ! [X9,X10] : k3_xboole_0(X9,X10) = k3_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | r1_tarski(X13,X11)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r1_tarski(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k1_zfmisc_1(X11) )
      & ( ~ r2_hidden(esk3_2(X15,X16),X16)
        | ~ r1_tarski(esk3_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) )
      & ( r2_hidden(esk3_2(X15,X16),X16)
        | r1_tarski(esk3_2(X15,X16),X15)
        | X16 = k1_zfmisc_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_11,negated_conjecture,(
    k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0)) != k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_12,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk4_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk4_3(X23,X24,X25),X23)
        | ~ r2_hidden(esk4_3(X23,X24,X25),X24)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X23)
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X24)
        | r2_hidden(esk4_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_tarski(X33,X34)
      | ~ r1_tarski(X34,X35)
      | r1_tarski(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0)) != k3_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0)))
    | r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(esk2_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | ~ r1_tarski(X30,X32)
      | r1_tarski(X30,k3_xboole_0(X31,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(esk1_0,esk2_0))
    | r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0)))
    | r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(esk1_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_23])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(esk1_0,esk2_0))
    | r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(X1,esk2_0))
    | ~ r1_tarski(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k3_xboole_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk4_3(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(k3_xboole_0(esk1_0,esk2_0))),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40])]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
