%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t70_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:11 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 ( 243 expanded)
%              Number of clauses        :   18 ( 103 expanded)
%              Number of leaves         :    2 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   72 (1192 expanded)
%              Number of equality atoms :   39 ( 625 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t70_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t70_zfmisc_1.p',t70_zfmisc_1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t70_zfmisc_1.p',l38_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
      <=> ( ~ r2_hidden(X1,X3)
          & ( r2_hidden(X2,X3)
            | X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t70_zfmisc_1])).

fof(c_0_3,negated_conjecture,
    ( ( ~ r2_hidden(esk2_0,esk3_0)
      | r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) )
    & ( esk1_0 != esk2_0
      | r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) )
    & ( ~ r2_hidden(esk1_0,esk3_0)
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | esk1_0 = esk2_0
      | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_2])])])])])).

fof(c_0_4,plain,(
    ! [X18,X19,X20] :
      ( ( ~ r2_hidden(X18,X20)
        | k4_xboole_0(k2_tarski(X18,X19),X20) != k1_tarski(X18) )
      & ( r2_hidden(X19,X20)
        | X18 = X19
        | k4_xboole_0(k2_tarski(X18,X19),X20) != k1_tarski(X18) )
      & ( ~ r2_hidden(X19,X20)
        | r2_hidden(X18,X20)
        | k4_xboole_0(k2_tarski(X18,X19),X20) = k1_tarski(X18) )
      & ( X18 != X19
        | r2_hidden(X18,X20)
        | k4_xboole_0(k2_tarski(X18,X19),X20) = k1_tarski(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

cnf(c_0_5,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk3_0)
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r2_hidden(X3,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | X3 = X1
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | esk1_0 = esk2_0
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_9,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0)
    | ~ r2_hidden(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_12,negated_conjecture,
    ( esk2_0 = esk1_0
    | r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0)
    | esk1_0 != esk2_0
    | k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) != k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) = k1_tarski(esk1_0)
    | esk2_0 = esk1_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk2_0),esk3_0) != k1_tarski(esk1_0)
    | esk2_0 != esk1_0 ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( esk2_0 = esk1_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_19,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk1_0,esk1_0),esk3_0) != k1_tarski(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_17])])).

cnf(c_0_20,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k1_tarski(X1)
    | r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_17]),c_0_21])]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
