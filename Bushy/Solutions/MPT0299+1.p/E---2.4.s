%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t107_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:57 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   13 (  24 expanded)
%              Number of clauses        :    8 (   9 expanded)
%              Number of leaves         :    2 (   6 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  61 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t107_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
     => r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X4,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t107_zfmisc_1.p',t107_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t107_zfmisc_1.p',l54_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
       => r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X4,X3)) ) ),
    inference(assume_negation,[status(cth)],[t107_zfmisc_1])).

fof(c_0_3,plain,(
    ! [X11,X12,X13,X14] :
      ( ( r2_hidden(X11,X13)
        | ~ r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) )
      & ( r2_hidden(X12,X14)
        | ~ r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) )
      & ( ~ r2_hidden(X11,X13)
        | ~ r2_hidden(X12,X14)
        | r2_hidden(k4_tarski(X11,X12),k2_zfmisc_1(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_4,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0))
    & ~ r2_hidden(k4_tarski(esk2_0,esk1_0),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk2_0,esk1_0),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
