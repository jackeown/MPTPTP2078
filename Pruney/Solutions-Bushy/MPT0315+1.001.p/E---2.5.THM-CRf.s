%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0315+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:24 EST 2020

% Result     : Theorem 0.24s
% Output     : CNFRefutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   20 (  37 expanded)
%              Number of clauses        :   13 (  16 expanded)
%              Number of leaves         :    3 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 106 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t104_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
        & ! [X6,X7] :
            ~ ( X1 = k4_tarski(X6,X7)
              & r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(t127_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(c_0_3,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk3_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_4,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( X8 = k4_tarski(esk1_5(X8,X9,X10,X11,X12),esk2_5(X8,X9,X10,X11,X12))
        | ~ r2_hidden(X8,k3_xboole_0(k2_zfmisc_1(X9,X10),k2_zfmisc_1(X11,X12))) )
      & ( r2_hidden(esk1_5(X8,X9,X10,X11,X12),k3_xboole_0(X9,X11))
        | ~ r2_hidden(X8,k3_xboole_0(k2_zfmisc_1(X9,X10),k2_zfmisc_1(X11,X12))) )
      & ( r2_hidden(esk2_5(X8,X9,X10,X11,X12),k3_xboole_0(X10,X12))
        | ~ r2_hidden(X8,k3_xboole_0(k2_zfmisc_1(X9,X10),k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t104_zfmisc_1])])])])).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_xboole_0(X1,X2)
          | r1_xboole_0(X3,X4) )
       => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    inference(assume_negation,[status(cth)],[t127_zfmisc_1])).

cnf(c_0_6,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,negated_conjecture,
    ( ( r1_xboole_0(esk4_0,esk5_0)
      | r1_xboole_0(esk6_0,esk7_0) )
    & ~ r1_xboole_0(k2_zfmisc_1(esk4_0,esk6_0),k2_zfmisc_1(esk5_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5))) ),
    inference(spm,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_3])).

cnf(c_0_11,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),k3_xboole_0(X3,X5))
    | ~ r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_xboole_0(k2_zfmisc_1(esk4_0,esk6_0),k2_zfmisc_1(esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k3_xboole_0(k2_zfmisc_1(X4,X1),k2_zfmisc_1(X5,X2))) ),
    inference(spm,[status(thm)],[c_0_6,c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0)
    | r1_xboole_0(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r1_xboole_0(X2,X4) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_xboole_0(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_17]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
