%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0299+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
       => r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X4,X3)) ) ),
    inference(assume_negation,[status(cth)],[t107_zfmisc_1])).

fof(c_0_3,plain,(
    ! [X1057,X1058,X1059,X1060] :
      ( ( r2_hidden(X1057,X1059)
        | ~ r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) )
      & ( r2_hidden(X1058,X1060)
        | ~ r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) )
      & ( ~ r2_hidden(X1057,X1059)
        | ~ r2_hidden(X1058,X1060)
        | r2_hidden(k4_tarski(X1057,X1058),k2_zfmisc_1(X1059,X1060)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_4,negated_conjecture,
    ( r2_hidden(k4_tarski(esk37_0,esk38_0),k2_zfmisc_1(esk39_0,esk40_0))
    & ~ r2_hidden(k4_tarski(esk38_0,esk37_0),k2_zfmisc_1(esk40_0,esk39_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r2_hidden(k4_tarski(esk37_0,esk38_0),k2_zfmisc_1(esk39_0,esk40_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk38_0,esk37_0),k2_zfmisc_1(esk40_0,esk39_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk37_0,esk39_0) ),
    inference(spm,[status(thm)],[c_0_5,c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk38_0,esk40_0) ),
    inference(spm,[status(thm)],[c_0_7,c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
