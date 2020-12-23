%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t82_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:12 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  75 expanded)
%              Number of clauses        :   28 (  36 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 211 expanded)
%              Number of equality atoms :   30 (  59 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',d3_xboole_0)).

fof(t82_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
     => r3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',t82_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',d10_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',t7_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(d9_xboole_0,axiom,(
    ! [X1,X2] :
      ( r3_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        | r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t82_zfmisc_1.p',d9_xboole_0)).

fof(c_0_7,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( ~ r2_hidden(esk4_3(X25,X26,X27),X26)
        | ~ r2_hidden(esk4_3(X25,X26,X27),X27)
        | X27 = k2_xboole_0(X25,X26) )
      & ( r2_hidden(esk4_3(X25,X26,X27),X27)
        | r2_hidden(esk4_3(X25,X26,X27),X25)
        | r2_hidden(esk4_3(X25,X26,X27),X26)
        | X27 = k2_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) = k1_zfmisc_1(k2_xboole_0(X1,X2))
       => r3_xboole_0(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t82_zfmisc_1])).

fof(c_0_9,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | r1_tarski(X15,X13)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r1_tarski(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k1_zfmisc_1(X13) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r1_tarski(esk3_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) )
      & ( r2_hidden(esk3_2(X17,X18),X18)
        | r1_tarski(esk3_2(X17,X18),X17)
        | X18 = k1_zfmisc_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)) = k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))
    & ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( k2_xboole_0(k1_zfmisc_1(esk1_0),k1_zfmisc_1(esk2_0)) = k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk2_0))
    | r2_hidden(X1,k1_zfmisc_1(esk1_0))
    | ~ r2_hidden(X1,k1_zfmisc_1(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X39,X40] : r1_tarski(X39,k2_xboole_0(X39,X40)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_23,plain,(
    ! [X9,X10] : k2_xboole_0(X9,X10) = k2_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_24,plain,(
    ! [X29,X30] :
      ( ( ~ r3_xboole_0(X29,X30)
        | r1_tarski(X29,X30)
        | r1_tarski(X30,X29) )
      & ( ~ r1_tarski(X29,X30)
        | r3_xboole_0(X29,X30) )
      & ( ~ r1_tarski(X30,X29)
        | r3_xboole_0(X29,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_xboole_0])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0))
    | r2_hidden(k2_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk1_0,esk2_0),esk2_0)
    | r2_hidden(k2_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( r3_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk2_0
    | r2_hidden(k2_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( ~ r3_xboole_0(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( r3_xboole_0(X2,X1)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k2_xboole_0(esk1_0,esk2_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_38,plain,
    ( r3_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk1_0,esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_37])).

cnf(c_0_40,plain,
    ( r3_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( k2_xboole_0(esk1_0,esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_39]),c_0_27])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
