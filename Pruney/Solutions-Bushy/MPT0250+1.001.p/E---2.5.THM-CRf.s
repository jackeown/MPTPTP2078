%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0250+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:17 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :    9 (  12 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    2 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(l20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
     => r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2)
       => r2_hidden(X1,X2) ) ),
    inference(assume_negation,[status(cth)],[t45_zfmisc_1])).

fof(c_0_3,plain,(
    ! [X3,X4] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X3),X4),X4)
      | r2_hidden(X3,X4) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l20_zfmisc_1])])).

fof(c_0_4,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk1_0),esk2_0),esk2_0)
    & ~ r2_hidden(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

cnf(c_0_5,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(X1),X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,negated_conjecture,
    ( r1_tarski(k2_xboole_0(k1_tarski(esk1_0),esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( ~ r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7]),
    [proof]).

%------------------------------------------------------------------------------
