%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t8_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   15 (  21 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  49 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t8_setfam_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t1_xboole_1)).

fof(t4_setfam_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(k1_setfam_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t8_setfam_1.p',t4_setfam_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r1_tarski(X1,X3) )
       => r1_tarski(k1_setfam_1(X2),X3) ) ),
    inference(assume_negation,[status(cth)],[t8_setfam_1])).

fof(c_0_4,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_5,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & r1_tarski(esk1_0,esk3_0)
    & ~ r1_tarski(k1_setfam_1(esk2_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X20,X21] :
      ( ~ r2_hidden(X20,X21)
      | r1_tarski(k1_setfam_1(X21),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_setfam_1])])).

cnf(c_0_7,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( r1_tarski(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r1_tarski(k1_setfam_1(X2),X1)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(k1_setfam_1(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
