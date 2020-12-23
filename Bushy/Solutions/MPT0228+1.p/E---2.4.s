%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t23_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:04 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  85 expanded)
%              Number of equality atoms :   39 (  58 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != X2
     => k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t23_zfmisc_1.p',t23_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t23_zfmisc_1.p',d1_tarski)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t23_zfmisc_1.p',commutativity_k2_tarski)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t23_zfmisc_1.p',l38_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != X2
       => k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X2)) = k1_tarski(X1) ) ),
    inference(assume_negation,[status(cth)],[t23_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk3_2(X14,X15),X15)
        | esk3_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk3_2(X14,X15),X15)
        | esk3_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,negated_conjecture,
    ( esk1_0 != esk2_0
    & k4_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk2_0)) != k1_tarski(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_tarski(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X19)
        | k4_xboole_0(k2_tarski(X17,X18),X19) != k1_tarski(X17) )
      & ( r2_hidden(X18,X19)
        | X17 = X18
        | k4_xboole_0(k2_tarski(X17,X18),X19) != k1_tarski(X17) )
      & ( ~ r2_hidden(X18,X19)
        | r2_hidden(X17,X19)
        | k4_xboole_0(k2_tarski(X17,X18),X19) = k1_tarski(X17) )
      & ( X17 != X18
        | r2_hidden(X17,X19)
        | k4_xboole_0(k2_tarski(X17,X18),X19) = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk2_0)) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk2_0,esk1_0),k1_tarski(esk2_0)) != k1_tarski(esk1_0) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X2)
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_0,k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_19,negated_conjecture,
    ( esk1_0 = X1
    | k1_tarski(esk2_0) != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,negated_conjecture,
    ( esk1_0 != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
