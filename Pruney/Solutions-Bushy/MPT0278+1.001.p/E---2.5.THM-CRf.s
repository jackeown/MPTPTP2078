%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0278+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:21 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  30 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 (  96 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r1_tarski(X1,X2)
       => r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t79_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X4,X5,X6,X7,X8,X9] :
      ( ( ~ r2_hidden(X6,X5)
        | r1_tarski(X6,X4)
        | X5 != k1_zfmisc_1(X4) )
      & ( ~ r1_tarski(X7,X4)
        | r2_hidden(X7,X5)
        | X5 != k1_zfmisc_1(X4) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | ~ r1_tarski(esk1_2(X8,X9),X8)
        | X9 = k1_zfmisc_1(X8) )
      & ( r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(esk1_2(X8,X9),X8)
        | X9 = k1_zfmisc_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_6,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_7,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk2_2(k1_zfmisc_1(esk3_0),X1),esk4_0)
    | r1_tarski(k1_zfmisc_1(esk3_0),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk3_0),X1)
    | r2_hidden(esk2_2(k1_zfmisc_1(esk3_0),X1),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk3_0),k1_zfmisc_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),
    [proof]).

%------------------------------------------------------------------------------
