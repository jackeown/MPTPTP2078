%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0917+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:57 EST 2020

% Result     : Theorem 10.34s
% Output     : CNFRefutation 10.34s
% Verified   : 
% Statistics : Number of formulae       :   26 (  49 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :    4 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 ( 123 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_mcart_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4)
        & r1_tarski(X5,X6) )
     => r1_tarski(k3_zfmisc_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_mcart_1)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t118_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT002+2.ax',t1_xboole_1)).

fof(d3_zfmisc_1,axiom,(
    ! [X1,X2,X3] : k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4)
          & r1_tarski(X5,X6) )
       => r1_tarski(k3_zfmisc_1(X1,X3,X5),k3_zfmisc_1(X2,X4,X6)) ) ),
    inference(assume_negation,[status(cth)],[t77_mcart_1])).

fof(c_0_5,plain,(
    ! [X190,X191,X192] :
      ( ( r1_tarski(k2_zfmisc_1(X190,X192),k2_zfmisc_1(X191,X192))
        | ~ r1_tarski(X190,X191) )
      & ( r1_tarski(k2_zfmisc_1(X192,X190),k2_zfmisc_1(X192,X191))
        | ~ r1_tarski(X190,X191) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

fof(c_0_6,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0)
    & r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk5_0,esk6_0)
    & ~ r1_tarski(k3_zfmisc_1(esk1_0,esk3_0,esk5_0),k3_zfmisc_1(esk2_0,esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X65,X66,X67] :
      ( ~ r1_tarski(X65,X66)
      | ~ r1_tarski(X66,X67)
      | r1_tarski(X65,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_8,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,X1),k2_zfmisc_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,X2))
    | ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,X2)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk3_0),k2_zfmisc_1(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X443,X444,X445] : k3_zfmisc_1(X443,X444,X445) = k2_zfmisc_1(k2_zfmisc_1(X443,X444),X445) ),
    inference(variable_rename,[status(thm)],[d3_zfmisc_1])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk5_0),k2_zfmisc_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(k3_zfmisc_1(esk1_0,esk3_0,esk5_0),k3_zfmisc_1(esk2_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
    ( k3_zfmisc_1(X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(X2,esk6_0))
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0),X1),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0),X1)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0),esk5_0),k2_zfmisc_1(k2_zfmisc_1(esk2_0,esk4_0),esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
