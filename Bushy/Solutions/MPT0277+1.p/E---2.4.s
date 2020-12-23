%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t75_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 396 expanded)
%              Number of clauses        :   26 ( 173 expanded)
%              Number of leaves         :    5 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  105 (1905 expanded)
%              Number of equality atoms :   87 (1556 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',l45_zfmisc_1)).

fof(t75_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',t75_zfmisc_1)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',t37_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',commutativity_k2_tarski)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t75_zfmisc_1.p',t4_boole)).

fof(c_0_5,plain,(
    ! [X11,X12,X13] :
      ( ( ~ r1_tarski(X11,k2_tarski(X12,X13))
        | X11 = k1_xboole_0
        | X11 = k1_tarski(X12)
        | X11 = k1_tarski(X13)
        | X11 = k2_tarski(X12,X13) )
      & ( X11 != k1_xboole_0
        | r1_tarski(X11,k2_tarski(X12,X13)) )
      & ( X11 != k1_tarski(X12)
        | r1_tarski(X11,k2_tarski(X12,X13)) )
      & ( X11 != k1_tarski(X13)
        | r1_tarski(X11,k2_tarski(X12,X13)) )
      & ( X11 != k2_tarski(X12,X13)
        | r1_tarski(X11,k2_tarski(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(X1,k2_tarski(X2,X3)) = k1_xboole_0
      <=> ~ ( X1 != k1_xboole_0
            & X1 != k1_tarski(X2)
            & X1 != k1_tarski(X3)
            & X1 != k2_tarski(X2,X3) ) ) ),
    inference(assume_negation,[status(cth)],[t75_zfmisc_1])).

fof(c_0_7,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k1_tarski(esk2_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k1_tarski(esk3_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( esk1_0 != k2_tarski(esk2_0,esk3_0)
      | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 )
    & ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0
      | esk1_0 = k1_xboole_0
      | esk1_0 = k1_tarski(esk2_0)
      | esk1_0 = k1_tarski(esk3_0)
      | esk1_0 = k2_tarski(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_10,plain,(
    ! [X9,X10] : k2_tarski(X9,X10) = k2_tarski(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_11,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk1_0 = k1_tarski(esk2_0)
    | esk1_0 = k1_tarski(esk3_0)
    | esk1_0 = k2_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k4_xboole_0(k1_tarski(X1),k2_tarski(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | k1_tarski(esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != k1_tarski(esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(X1,esk3_0)) = k1_xboole_0
    | k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_23,plain,
    ( k4_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | k1_tarski(esk2_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( esk1_0 != k1_tarski(esk2_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( k4_xboole_0(esk1_0,k2_tarski(esk2_0,X1)) = k1_xboole_0
    | k2_tarski(esk2_0,esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( k2_tarski(esk2_0,esk3_0) = esk1_0
    | esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( esk1_0 != k2_tarski(esk2_0,esk3_0)
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( k4_xboole_0(esk1_0,esk1_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_32,plain,(
    ! [X17] : k4_xboole_0(k1_xboole_0,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_33,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k4_xboole_0(esk1_0,k2_tarski(esk2_0,esk3_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_31])).

cnf(c_0_35,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_34])]),
    [proof]).
%------------------------------------------------------------------------------
