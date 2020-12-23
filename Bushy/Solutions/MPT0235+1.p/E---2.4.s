%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t30_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:05 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   37 (  56 expanded)
%              Number of clauses        :   26 (  29 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 230 expanded)
%              Number of equality atoms :   83 ( 146 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',d2_tarski)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',l3_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',d1_zfmisc_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',commutativity_k2_tarski)).

fof(t30_zfmisc_1,conjecture,(
    ! [X1] : k1_zfmisc_1(k1_tarski(X1)) = k2_tarski(k1_xboole_0,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t30_zfmisc_1.p',t30_zfmisc_1)).

fof(c_0_5,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X17
        | X20 = X18
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X17
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k2_tarski(X17,X18) )
      & ( esk3_3(X22,X23,X24) != X22
        | ~ r2_hidden(esk3_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( esk3_3(X22,X23,X24) != X23
        | ~ r2_hidden(esk3_3(X22,X23,X24),X24)
        | X24 = k2_tarski(X22,X23) )
      & ( r2_hidden(esk3_3(X22,X23,X24),X24)
        | esk3_3(X22,X23,X24) = X22
        | esk3_3(X22,X23,X24) = X23
        | X24 = k2_tarski(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X26,X27] :
      ( ( ~ r1_tarski(X26,k1_tarski(X27))
        | X26 = k1_xboole_0
        | X26 = k1_tarski(X27) )
      & ( X26 != k1_xboole_0
        | r1_tarski(X26,k1_tarski(X27)) )
      & ( X26 != k1_tarski(X27)
        | r1_tarski(X26,k1_tarski(X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_7,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_tarski(esk2_2(X1,X2),X1)
    | X2 = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X2,X3)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( esk2_2(k1_tarski(X1),X2) = k1_tarski(X1)
    | esk2_2(k1_tarski(X1),X2) = k1_xboole_0
    | X2 = k1_zfmisc_1(k1_tarski(X1))
    | r2_hidden(esk2_2(k1_tarski(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( esk2_2(k1_tarski(X1),k2_tarski(X2,X3)) = k1_tarski(X1)
    | esk2_2(k1_tarski(X1),k2_tarski(X2,X3)) = k1_xboole_0
    | esk2_2(k1_tarski(X1),k2_tarski(X2,X3)) = X3
    | esk2_2(k1_tarski(X1),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k1_zfmisc_1(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_14,plain,
    ( esk2_2(k1_tarski(X1),k2_tarski(X2,X3)) = k1_tarski(X1)
    | esk2_2(k1_tarski(X1),k2_tarski(X2,X3)) = k1_xboole_0
    | esk2_2(k1_tarski(X1),k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k1_zfmisc_1(k1_tarski(X1))
    | X3 != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_13])).

cnf(c_0_15,plain,
    ( esk2_2(k1_tarski(X1),k2_tarski(X2,k1_xboole_0)) = k1_tarski(X1)
    | esk2_2(k1_tarski(X1),k2_tarski(X2,k1_xboole_0)) = k1_xboole_0
    | esk2_2(k1_tarski(X1),k2_tarski(X2,k1_xboole_0)) = X2
    | k2_tarski(X2,k1_xboole_0) = k1_zfmisc_1(k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_16,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_tarski(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,plain,
    ( X2 = k1_zfmisc_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r1_tarski(esk2_2(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,plain,
    ( esk2_2(k1_tarski(X1),k2_tarski(X2,k1_xboole_0)) = k1_xboole_0
    | esk2_2(k1_tarski(X1),k2_tarski(X2,k1_xboole_0)) = X2
    | k2_tarski(X2,k1_xboole_0) = k1_zfmisc_1(k1_tarski(X1))
    | k1_tarski(X1) != X2 ),
    inference(ef,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] : k1_zfmisc_1(k1_tarski(X1)) = k2_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(assume_negation,[status(cth)],[t30_zfmisc_1])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_26,plain,
    ( X1 = k1_zfmisc_1(k1_tarski(X2))
    | esk2_2(k1_tarski(X2),X1) != k1_tarski(X2)
    | ~ r2_hidden(esk2_2(k1_tarski(X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( esk2_2(k1_tarski(X1),k2_tarski(k1_xboole_0,k1_tarski(X1))) = k1_tarski(X1)
    | esk2_2(k1_tarski(X1),k2_tarski(k1_xboole_0,k1_tarski(X1))) = k1_xboole_0
    | k1_zfmisc_1(k1_tarski(X1)) = k2_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21]),c_0_21]),c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X1,X3) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_30,negated_conjecture,(
    k1_zfmisc_1(k1_tarski(esk1_0)) != k2_tarski(k1_xboole_0,k1_tarski(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_31,plain,
    ( X1 = k1_zfmisc_1(k1_tarski(X2))
    | esk2_2(k1_tarski(X2),X1) != k1_xboole_0
    | ~ r2_hidden(esk2_2(k1_tarski(X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_25])).

cnf(c_0_32,plain,
    ( esk2_2(k1_tarski(X1),k2_tarski(k1_xboole_0,k1_tarski(X1))) = k1_xboole_0
    | k1_zfmisc_1(k1_tarski(X1)) = k2_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k1_zfmisc_1(k1_tarski(esk1_0)) != k2_tarski(k1_xboole_0,k1_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( k1_zfmisc_1(k1_tarski(X1)) = k2_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
