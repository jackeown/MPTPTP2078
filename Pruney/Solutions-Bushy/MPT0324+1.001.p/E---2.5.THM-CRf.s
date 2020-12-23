%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0324+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   16 (  22 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   53 (  71 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t137_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
     => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(c_0_3,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k3_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k3_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_4,plain,(
    ! [X15,X16,X17,X18] : k2_zfmisc_1(k3_xboole_0(X15,X16),k3_xboole_0(X17,X18)) = k3_xboole_0(k2_zfmisc_1(X15,X17),k2_zfmisc_1(X16,X18)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ( ( r2_hidden(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X1,k2_zfmisc_1(X4,X5)) )
       => r2_hidden(X1,k2_zfmisc_1(k3_xboole_0(X2,X4),k3_xboole_0(X3,X5))) ) ),
    inference(assume_negation,[status(cth)],[t137_zfmisc_1])).

cnf(c_0_6,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r2_hidden(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r2_hidden(esk2_0,k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_zfmisc_1(k3_xboole_0(X3,X4),k3_xboole_0(X5,X6))
    | ~ r2_hidden(X1,k2_zfmisc_1(X4,X6))
    | ~ r2_hidden(X1,k2_zfmisc_1(X3,X5)) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | X1 != k2_zfmisc_1(k3_xboole_0(X2,esk5_0),k3_xboole_0(X3,esk6_0))
    | ~ r2_hidden(esk2_0,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk2_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk2_0,X1)
    | X1 != k2_zfmisc_1(k3_xboole_0(esk3_0,esk5_0),k3_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [proof]).

%------------------------------------------------------------------------------
