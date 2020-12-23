%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t14_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:02 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   18 (  21 expanded)
%              Number of clauses        :    9 (  10 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  48 expanded)
%              Number of equality atoms :   32 (  35 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t14_zfmisc_1.p',d2_tarski)).

fof(t14_zfmisc_1,conjecture,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t14_zfmisc_1.p',t14_zfmisc_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t14_zfmisc_1.p',l22_zfmisc_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t14_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(c_0_4,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X13
        | X16 = X14
        | X15 != k2_tarski(X13,X14) )
      & ( X17 != X13
        | r2_hidden(X17,X15)
        | X15 != k2_tarski(X13,X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k2_tarski(X13,X14) )
      & ( esk3_3(X18,X19,X20) != X18
        | ~ r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_tarski(X18,X19) )
      & ( esk3_3(X18,X19,X20) != X19
        | ~ r2_hidden(esk3_3(X18,X19,X20),X20)
        | X20 = k2_tarski(X18,X19) )
      & ( r2_hidden(esk3_3(X18,X19,X20),X20)
        | esk3_3(X18,X19,X20) = X18
        | esk3_3(X18,X19,X20) = X19
        | X20 = k2_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] : k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k2_tarski(X1,X2) ),
    inference(assume_negation,[status(cth)],[t14_zfmisc_1])).

fof(c_0_6,plain,(
    ! [X23,X24] :
      ( ~ r2_hidden(X23,X24)
      | k2_xboole_0(k1_tarski(X23),X24) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,(
    k2_xboole_0(k1_tarski(esk1_0),k2_tarski(esk1_0,esk2_0)) != k2_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X11,X12] : k2_xboole_0(X11,X12) = k2_xboole_0(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_10,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_7])])).

cnf(c_0_12,negated_conjecture,
    ( k2_xboole_0(k1_tarski(esk1_0),k2_tarski(esk1_0,esk2_0)) != k2_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k2_xboole_0(k1_tarski(X1),k2_tarski(X1,X2)) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( k2_xboole_0(k2_tarski(esk1_0,esk2_0),k1_tarski(esk1_0)) != k2_tarski(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X1)) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
