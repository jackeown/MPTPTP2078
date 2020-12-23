%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0222+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   14 (  17 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  42 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( X1 != X2
     => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( X1 != X2
       => r1_xboole_0(k1_tarski(X1),k1_tarski(X2)) ) ),
    inference(assume_negation,[status(cth)],[t17_zfmisc_1])).

fof(c_0_4,plain,(
    ! [X4,X5,X6,X7,X8,X9] :
      ( ( ~ r2_hidden(X6,X5)
        | X6 = X4
        | X5 != k1_tarski(X4) )
      & ( X7 != X4
        | r2_hidden(X7,X5)
        | X5 != k1_tarski(X4) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) != X8
        | X9 = k1_tarski(X8) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | esk1_2(X8,X9) = X8
        | X9 = k1_tarski(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_5,negated_conjecture,
    ( esk2_0 != esk3_0
    & ~ r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

fof(c_0_6,plain,(
    ! [X11,X12] :
      ( r2_hidden(X11,X12)
      | r1_xboole_0(k1_tarski(X11),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_7,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk2_0,k1_tarski(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),
    [proof]).

%------------------------------------------------------------------------------
