%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0383+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:32 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   26 (  59 expanded)
%              Number of clauses        :   17 (  24 expanded)
%              Number of leaves         :    4 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 243 expanded)
%              Number of equality atoms :    7 (  29 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_subset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X4,X3)
        & r1_tarski(X3,k2_zfmisc_1(X1,X2))
        & ! [X5] :
            ( m1_subset_1(X5,X1)
           => ! [X6] :
                ( m1_subset_1(X6,X2)
               => X4 != k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

fof(t103_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r2_hidden(X4,X3)
          & r1_tarski(X3,k2_zfmisc_1(X1,X2))
          & ! [X5] :
              ( m1_subset_1(X5,X1)
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => X4 != k4_tarski(X5,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_subset_1])).

fof(c_0_5,negated_conjecture,(
    ! [X21,X22] :
      ( r2_hidden(esk6_0,esk5_0)
      & r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))
      & ( ~ m1_subset_1(X21,esk3_0)
        | ~ m1_subset_1(X22,esk4_0)
        | esk6_0 != k4_tarski(X21,X22) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

fof(c_0_6,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r2_hidden(esk1_4(X9,X10,X11,X12),X10)
        | ~ r1_tarski(X9,k2_zfmisc_1(X10,X11))
        | ~ r2_hidden(X12,X9) )
      & ( r2_hidden(esk2_4(X9,X10,X11,X12),X11)
        | ~ r1_tarski(X9,k2_zfmisc_1(X10,X11))
        | ~ r2_hidden(X12,X9) )
      & ( X12 = k4_tarski(esk1_4(X9,X10,X11,X12),esk2_4(X9,X10,X11,X12))
        | ~ r1_tarski(X9,k2_zfmisc_1(X10,X11))
        | ~ r2_hidden(X12,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).

fof(c_0_7,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X8,X7)
        | r2_hidden(X8,X7)
        | v1_xboole_0(X7) )
      & ( ~ r2_hidden(X8,X7)
        | m1_subset_1(X8,X7)
        | v1_xboole_0(X7) )
      & ( ~ m1_subset_1(X8,X7)
        | v1_xboole_0(X8)
        | ~ v1_xboole_0(X7) )
      & ( ~ v1_xboole_0(X8)
        | m1_subset_1(X8,X7)
        | ~ v1_xboole_0(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_8,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_9,negated_conjecture,
    ( ~ m1_subset_1(X1,esk3_0)
    | ~ m1_subset_1(X2,esk4_0)
    | esk6_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( X1 = k4_tarski(esk1_4(X2,X3,X4,X1),esk2_4(X2,X3,X4,X1))
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(esk2_4(X1,X2,X3,esk6_0),esk4_0)
    | ~ m1_subset_1(esk1_4(X1,X2,X3,esk6_0),esk3_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk2_4(X1,X2,X3,esk6_0),esk4_0)
    | ~ r2_hidden(esk6_0,X1)
    | ~ m1_subset_1(esk1_4(X1,X2,X3,esk6_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_16,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(esk2_4(X1,X2,X3,esk6_0),esk4_0)
    | ~ r2_hidden(esk1_4(X1,X2,X3,esk6_0),esk3_0)
    | ~ r2_hidden(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X3)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk5_0,esk3_0,esk4_0,esk6_0),esk4_0)
    | ~ r2_hidden(esk1_4(esk5_0,esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk2_4(esk5_0,esk3_0,esk4_0,X1),esk4_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk1_4(esk5_0,esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_18])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk1_4(esk5_0,esk3_0,esk4_0,X1),esk3_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_18])]),
    [proof]).

%------------------------------------------------------------------------------
