%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t65_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:26 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  41 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 175 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   14 (   6 average)
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
    file('/export/starexec/sandbox/benchmark/subset_1__t65_subset_1.p',t65_subset_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t65_subset_1.p',d2_subset_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t65_subset_1.p',t7_boole)).

fof(t103_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/subset_1__t65_subset_1.p',t103_zfmisc_1)).

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

fof(c_0_5,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X16,X15)
        | r2_hidden(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ r2_hidden(X16,X15)
        | m1_subset_1(X16,X15)
        | v1_xboole_0(X15) )
      & ( ~ m1_subset_1(X16,X15)
        | v1_xboole_0(X16)
        | ~ v1_xboole_0(X15) )
      & ( ~ v1_xboole_0(X16)
        | m1_subset_1(X16,X15)
        | ~ v1_xboole_0(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_6,plain,(
    ! [X26,X27] :
      ( ~ r2_hidden(X26,X27)
      | ~ v1_xboole_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_7,negated_conjecture,(
    ! [X11,X12] :
      ( r2_hidden(esk4_0,esk3_0)
      & r1_tarski(esk3_0,k2_zfmisc_1(esk1_0,esk2_0))
      & ( ~ m1_subset_1(X11,esk1_0)
        | ~ m1_subset_1(X12,esk2_0)
        | esk4_0 != k4_tarski(X11,X12) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( ~ m1_subset_1(X1,esk1_0)
    | ~ m1_subset_1(X2,esk2_0)
    | esk4_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( k4_tarski(X1,X2) != esk4_0
    | ~ m1_subset_1(X1,esk1_0)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_13,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_hidden(esk6_4(X19,X20,X21,X22),X20)
        | ~ r1_tarski(X19,k2_zfmisc_1(X20,X21))
        | ~ r2_hidden(X22,X19) )
      & ( r2_hidden(esk7_4(X19,X20,X21,X22),X21)
        | ~ r1_tarski(X19,k2_zfmisc_1(X20,X21))
        | ~ r2_hidden(X22,X19) )
      & ( X22 = k4_tarski(esk6_4(X19,X20,X21,X22),esk7_4(X19,X20,X21,X22))
        | ~ r1_tarski(X19,k2_zfmisc_1(X20,X21))
        | ~ r2_hidden(X22,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_zfmisc_1])])])])).

cnf(c_0_14,negated_conjecture,
    ( k4_tarski(X1,X2) != esk4_0
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk7_4(X1,X2,X3,X4),X3)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( k4_tarski(X1,esk7_4(X2,X3,esk2_0,X4)) != esk4_0
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,esk2_0))
    | ~ r2_hidden(X1,esk1_0)
    | ~ r2_hidden(X4,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_17,plain,
    ( X1 = k4_tarski(esk6_4(X2,X3,X4,X1),esk7_4(X2,X3,X4,X1))
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(X2,esk2_0))
    | ~ r2_hidden(esk6_4(X1,X2,esk2_0,esk4_0),esk1_0)
    | ~ r2_hidden(esk4_0,X1) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r2_hidden(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r2_hidden(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
