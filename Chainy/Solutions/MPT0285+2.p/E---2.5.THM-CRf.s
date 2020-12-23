%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0285+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    9 (  12 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    2 (   3 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t92_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(c_0_2,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,X2)
       => r1_tarski(X1,k3_tarski(X2)) ) ),
    inference(assume_negation,[status(cth)],[t92_zfmisc_1])).

fof(c_0_3,negated_conjecture,
    ( r2_hidden(esk32_0,esk33_0)
    & ~ r1_tarski(esk32_0,k3_tarski(esk33_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_2])])])).

fof(c_0_4,plain,(
    ! [X1053,X1054] :
      ( ~ r2_hidden(X1053,X1054)
      | r1_tarski(X1053,k3_tarski(X1054)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_5,negated_conjecture,
    ( ~ r1_tarski(esk32_0,k3_tarski(esk33_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_6,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( r2_hidden(esk32_0,esk33_0) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_8,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_5,c_0_6]),c_0_7])]),
    [proof]).
%------------------------------------------------------------------------------
