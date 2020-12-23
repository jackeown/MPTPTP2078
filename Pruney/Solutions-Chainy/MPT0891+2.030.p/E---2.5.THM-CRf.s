%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:56 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 723 expanded)
%              Number of clauses        :   39 ( 255 expanded)
%              Number of leaves         :   11 ( 181 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 (3267 expanded)
%              Number of equality atoms :  115 (2704 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_mcart_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                & X4 != k6_mcart_1(X1,X2,X3,X4)
                & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

fof(t41_mcart_1,axiom,(
    ! [X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_mcart_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t50_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => ( k5_mcart_1(X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(X4))
                & k6_mcart_1(X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(t49_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))
          & ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))
          & ~ r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(t48_mcart_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0
        & ~ ! [X4] :
              ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
             => X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(l29_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( X1 != k1_xboole_0
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0
          & ~ ! [X4] :
                ( m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))
               => ( X4 != k5_mcart_1(X1,X2,X3,X4)
                  & X4 != k6_mcart_1(X1,X2,X3,X4)
                  & X4 != k7_mcart_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_mcart_1])).

fof(c_0_12,plain,(
    ! [X14,X15,X16,X17] : k3_zfmisc_1(k1_tarski(X14),k2_tarski(X15,X16),k1_tarski(X17)) = k2_tarski(k3_mcart_1(X14,X15,X17),k3_mcart_1(X14,X16,X17)) ),
    inference(variable_rename,[status(thm)],[t41_mcart_1])).

fof(c_0_13,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X25,X26,X27,X28] :
      ( ( k5_mcart_1(X25,X26,X27,X28) = k1_mcart_1(k1_mcart_1(X28))
        | ~ m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k6_mcart_1(X25,X26,X27,X28) = k2_mcart_1(k1_mcart_1(X28))
        | ~ m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 )
      & ( k7_mcart_1(X25,X26,X27,X28) = k2_mcart_1(X28)
        | ~ m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))
        | X25 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).

fof(c_0_15,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk3_0 != k1_xboole_0
    & m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))
    & ( esk4_0 = k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
      | esk4_0 = k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
      | esk4_0 = k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_16,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r1_tarski(X22,k3_zfmisc_1(X22,X23,X24))
        | X22 = k1_xboole_0 )
      & ( ~ r1_tarski(X22,k3_zfmisc_1(X23,X24,X22))
        | X22 = k1_xboole_0 )
      & ( ~ r1_tarski(X22,k3_zfmisc_1(X24,X22,X23))
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).

cnf(c_0_17,plain,
    ( k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X21] :
      ( X18 = k1_xboole_0
      | X19 = k1_xboole_0
      | X20 = k1_xboole_0
      | ~ m1_subset_1(X21,k3_zfmisc_1(X18,X19,X20))
      | X21 = k3_mcart_1(k5_mcart_1(X18,X19,X20,X21),k6_mcart_1(X18,X19,X20,X21),k7_mcart_1(X18,X19,X20,X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).

cnf(c_0_20,plain,
    ( k7_mcart_1(X1,X2,X3,X4) = k2_mcart_1(X4)
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X2,X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X3),k2_tarski(X4,X4)) = k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | X4 = k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))
    | ~ m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = k2_mcart_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24])).

fof(c_0_29,plain,(
    ! [X10,X11] :
      ( ( ~ r1_tarski(X10,k1_tarski(X11))
        | X10 = k1_xboole_0
        | X10 = k1_tarski(X11) )
      & ( X10 != k1_xboole_0
        | r1_tarski(X10,k1_tarski(X11)) )
      & ( X10 != k1_tarski(X11)
        | r1_tarski(X10,k1_tarski(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X1,X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X2) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(X1,X2),k2_tarski(k3_mcart_1(X3,X1,X4),k3_mcart_1(X3,X2,X4))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_mcart_1(esk4_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_28]),c_0_22]),c_0_23]),c_0_24])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k3_zfmisc_1(X2,X3,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(X1,X1),k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X4,X3))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( k2_tarski(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1),k2_tarski(esk4_0,k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1,k2_mcart_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 = k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | esk4_0 = k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | esk4_0 = k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_tarski(X2,X2))
    | X1 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_18]),c_0_18])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X1) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(X1,X1),k2_tarski(k3_mcart_1(X2,X3,X1),k3_mcart_1(X2,X4,X1))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( k2_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_tarski(esk4_0,k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1,k2_mcart_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k2_tarski(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_tarski(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk4_0
    | k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk4_0
    | k2_mcart_1(esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X8,X9] :
      ( k3_xboole_0(X8,k1_tarski(X9)) != k1_tarski(X9)
      | r2_hidden(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).

cnf(c_0_45,negated_conjecture,
    ( k2_tarski(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0)) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0)),k2_tarski(esk4_0,k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1,k2_mcart_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( k2_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_tarski(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_47,negated_conjecture,
    ( k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0) = esk4_0
    | k2_tarski(esk4_0,esk4_0) = k1_xboole_0
    | k2_mcart_1(esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])])).

fof(c_0_48,plain,(
    ! [X12,X13] :
      ( ( k4_xboole_0(X12,k1_tarski(X13)) != X12
        | ~ r2_hidden(X13,X12) )
      & ( r2_hidden(X13,X12)
        | k4_xboole_0(X12,k1_tarski(X13)) = X12 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_49,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k1_tarski(X2)) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k2_tarski(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0)) = k1_xboole_0
    | ~ r1_tarski(k2_tarski(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0)),k2_tarski(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( k2_tarski(esk4_0,esk4_0) = k1_xboole_0
    | k2_mcart_1(esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_43])])).

fof(c_0_52,plain,(
    ! [X5] : k3_xboole_0(X5,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_54,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_55,plain,
    ( r2_hidden(X2,X1)
    | k3_xboole_0(X1,k2_tarski(X2,X2)) != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_18]),c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( k2_tarski(esk4_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_43])])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,k2_tarski(X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_18])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_56]),c_0_59])]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:41:39 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.18/0.36  # and selection function SelectNegativeLiterals.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.027 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t51_mcart_1, conjecture, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 0.18/0.36  fof(t41_mcart_1, axiom, ![X1, X2, X3, X4]:k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k1_tarski(X4))=k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_mcart_1)).
% 0.18/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.36  fof(t50_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((k5_mcart_1(X1,X2,X3,X4)=k1_mcart_1(k1_mcart_1(X4))&k6_mcart_1(X1,X2,X3,X4)=k2_mcart_1(k1_mcart_1(X4)))&k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 0.18/0.36  fof(t49_mcart_1, axiom, ![X1, X2, X3]:(~(((~(r1_tarski(X1,k3_zfmisc_1(X1,X2,X3)))&~(r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))))&~(r1_tarski(X1,k3_zfmisc_1(X3,X1,X2)))))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_mcart_1)).
% 0.18/0.36  fof(t48_mcart_1, axiom, ![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 0.18/0.36  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.18/0.36  fof(l29_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 0.18/0.36  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.18/0.36  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.18/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.18/0.36  fof(c_0_11, negated_conjecture, ~(![X1, X2, X3]:~((((X1!=k1_xboole_0&X2!=k1_xboole_0)&X3!=k1_xboole_0)&~(![X4]:(m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))=>((X4!=k5_mcart_1(X1,X2,X3,X4)&X4!=k6_mcart_1(X1,X2,X3,X4))&X4!=k7_mcart_1(X1,X2,X3,X4))))))), inference(assume_negation,[status(cth)],[t51_mcart_1])).
% 0.18/0.36  fof(c_0_12, plain, ![X14, X15, X16, X17]:k3_zfmisc_1(k1_tarski(X14),k2_tarski(X15,X16),k1_tarski(X17))=k2_tarski(k3_mcart_1(X14,X15,X17),k3_mcart_1(X14,X16,X17)), inference(variable_rename,[status(thm)],[t41_mcart_1])).
% 0.18/0.36  fof(c_0_13, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.36  fof(c_0_14, plain, ![X25, X26, X27, X28]:(((k5_mcart_1(X25,X26,X27,X28)=k1_mcart_1(k1_mcart_1(X28))|~m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0))&(k6_mcart_1(X25,X26,X27,X28)=k2_mcart_1(k1_mcart_1(X28))|~m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0)))&(k7_mcart_1(X25,X26,X27,X28)=k2_mcart_1(X28)|~m1_subset_1(X28,k3_zfmisc_1(X25,X26,X27))|(X25=k1_xboole_0|X26=k1_xboole_0|X27=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t50_mcart_1])])])])).
% 0.18/0.36  fof(c_0_15, negated_conjecture, (((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk3_0!=k1_xboole_0)&(m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))&(esk4_0=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk4_0=k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk4_0=k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.18/0.36  fof(c_0_16, plain, ![X22, X23, X24]:(((~r1_tarski(X22,k3_zfmisc_1(X22,X23,X24))|X22=k1_xboole_0)&(~r1_tarski(X22,k3_zfmisc_1(X23,X24,X22))|X22=k1_xboole_0))&(~r1_tarski(X22,k3_zfmisc_1(X24,X22,X23))|X22=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_mcart_1])])])])).
% 0.18/0.36  cnf(c_0_17, plain, (k3_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3),k1_tarski(X4))=k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.36  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.36  fof(c_0_19, plain, ![X18, X19, X20, X21]:(X18=k1_xboole_0|X19=k1_xboole_0|X20=k1_xboole_0|(~m1_subset_1(X21,k3_zfmisc_1(X18,X19,X20))|X21=k3_mcart_1(k5_mcart_1(X18,X19,X20,X21),k6_mcart_1(X18,X19,X20,X21),k7_mcart_1(X18,X19,X20,X21)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_mcart_1])])])).
% 0.18/0.36  cnf(c_0_20, plain, (k7_mcart_1(X1,X2,X3,X4)=k2_mcart_1(X4)|X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k3_zfmisc_1(esk1_0,esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_22, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_23, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_24, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_25, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_zfmisc_1(X2,X1,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_26, plain, (k3_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X3),k2_tarski(X4,X4))=k2_tarski(k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.18/0.36  cnf(c_0_27, plain, (X1=k1_xboole_0|X2=k1_xboole_0|X3=k1_xboole_0|X4=k3_mcart_1(k5_mcart_1(X1,X2,X3,X4),k6_mcart_1(X1,X2,X3,X4),k7_mcart_1(X1,X2,X3,X4))|~m1_subset_1(X4,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=k2_mcart_1(esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24])).
% 0.18/0.36  fof(c_0_29, plain, ![X10, X11]:((~r1_tarski(X10,k1_tarski(X11))|(X10=k1_xboole_0|X10=k1_tarski(X11)))&((X10!=k1_xboole_0|r1_tarski(X10,k1_tarski(X11)))&(X10!=k1_tarski(X11)|r1_tarski(X10,k1_tarski(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.18/0.36  cnf(c_0_30, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_zfmisc_1(X1,X2,X3))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_31, plain, (k2_tarski(X1,X2)=k1_xboole_0|~r1_tarski(k2_tarski(X1,X2),k2_tarski(k3_mcart_1(X3,X1,X4),k3_mcart_1(X3,X2,X4)))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k2_mcart_1(esk4_0))=esk4_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_28]), c_0_22]), c_0_23]), c_0_24])).
% 0.18/0.36  cnf(c_0_33, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.36  cnf(c_0_34, plain, (X1=k1_xboole_0|~r1_tarski(X1,k3_zfmisc_1(X2,X3,X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_xboole_0|~r1_tarski(k2_tarski(X1,X1),k2_tarski(k3_mcart_1(X1,X2,X3),k3_mcart_1(X1,X4,X3)))), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.18/0.36  cnf(c_0_36, negated_conjecture, (k2_tarski(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)=k1_xboole_0|~r1_tarski(k2_tarski(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1),k2_tarski(esk4_0,k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1,k2_mcart_1(esk4_0))))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.36  cnf(c_0_37, negated_conjecture, (esk4_0=k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk4_0=k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)|esk4_0=k7_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_38, plain, (r1_tarski(X1,k2_tarski(X2,X2))|X1!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_18]), c_0_18])).
% 0.18/0.36  cnf(c_0_39, plain, (k2_tarski(X1,X1)=k1_xboole_0|~r1_tarski(k2_tarski(X1,X1),k2_tarski(k3_mcart_1(X2,X3,X1),k3_mcart_1(X2,X4,X1)))), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.18/0.36  cnf(c_0_40, negated_conjecture, (k2_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0))=k1_xboole_0|~r1_tarski(k2_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_tarski(esk4_0,k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1,k2_mcart_1(esk4_0))))), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.18/0.36  cnf(c_0_41, negated_conjecture, (k2_tarski(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0))=k1_xboole_0|~r1_tarski(k2_tarski(k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_tarski(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_36, c_0_32])).
% 0.18/0.36  cnf(c_0_42, negated_conjecture, (k6_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk4_0|k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk4_0|k2_mcart_1(esk4_0)=esk4_0), inference(spm,[status(thm)],[c_0_37, c_0_28])).
% 0.18/0.36  cnf(c_0_43, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1))), inference(er,[status(thm)],[c_0_38])).
% 0.18/0.36  fof(c_0_44, plain, ![X8, X9]:(k3_xboole_0(X8,k1_tarski(X9))!=k1_tarski(X9)|r2_hidden(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l29_zfmisc_1])])).
% 0.18/0.36  cnf(c_0_45, negated_conjecture, (k2_tarski(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0))=k1_xboole_0|~r1_tarski(k2_tarski(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0)),k2_tarski(esk4_0,k3_mcart_1(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),X1,k2_mcart_1(esk4_0))))), inference(spm,[status(thm)],[c_0_39, c_0_32])).
% 0.18/0.36  cnf(c_0_46, negated_conjecture, (k2_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0))=k1_xboole_0|~r1_tarski(k2_tarski(k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0),k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)),k2_tarski(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_32])).
% 0.18/0.36  cnf(c_0_47, negated_conjecture, (k5_mcart_1(esk1_0,esk2_0,esk3_0,esk4_0)=esk4_0|k2_tarski(esk4_0,esk4_0)=k1_xboole_0|k2_mcart_1(esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])])).
% 0.18/0.36  fof(c_0_48, plain, ![X12, X13]:((k4_xboole_0(X12,k1_tarski(X13))!=X12|~r2_hidden(X13,X12))&(r2_hidden(X13,X12)|k4_xboole_0(X12,k1_tarski(X13))=X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.18/0.36  cnf(c_0_49, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k1_tarski(X2))!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.36  cnf(c_0_50, negated_conjecture, (k2_tarski(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0))=k1_xboole_0|~r1_tarski(k2_tarski(k2_mcart_1(esk4_0),k2_mcart_1(esk4_0)),k2_tarski(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_32])).
% 0.18/0.36  cnf(c_0_51, negated_conjecture, (k2_tarski(esk4_0,esk4_0)=k1_xboole_0|k2_mcart_1(esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_43])])).
% 0.18/0.36  fof(c_0_52, plain, ![X5]:k3_xboole_0(X5,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.18/0.36  cnf(c_0_53, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.36  fof(c_0_54, plain, ![X6]:k4_xboole_0(X6,k1_xboole_0)=X6, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.18/0.36  cnf(c_0_55, plain, (r2_hidden(X2,X1)|k3_xboole_0(X1,k2_tarski(X2,X2))!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_18]), c_0_18])).
% 0.18/0.36  cnf(c_0_56, negated_conjecture, (k2_tarski(esk4_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_43])])).
% 0.18/0.36  cnf(c_0_57, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.18/0.36  cnf(c_0_58, plain, (k4_xboole_0(X1,k2_tarski(X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[c_0_53, c_0_18])).
% 0.18/0.36  cnf(c_0_59, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.36  cnf(c_0_60, negated_conjecture, (r2_hidden(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.18/0.36  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_56]), c_0_59])]), c_0_60])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 62
% 0.18/0.36  # Proof object clause steps            : 39
% 0.18/0.36  # Proof object formula steps           : 23
% 0.18/0.36  # Proof object conjectures             : 22
% 0.18/0.36  # Proof object clause conjectures      : 19
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 17
% 0.18/0.36  # Proof object initial formulas used   : 11
% 0.18/0.36  # Proof object generating inferences   : 17
% 0.18/0.36  # Proof object simplifying inferences  : 27
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 11
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 22
% 0.18/0.36  # Removed in clause preprocessing      : 1
% 0.18/0.36  # Initial clauses in saturation        : 21
% 0.18/0.36  # Processed clauses                    : 74
% 0.18/0.36  # ...of these trivial                  : 1
% 0.18/0.36  # ...subsumed                          : 4
% 0.18/0.36  # ...remaining for further processing  : 68
% 0.18/0.36  # Other redundant clauses eliminated   : 2
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 1
% 0.18/0.36  # Backward-rewritten                   : 4
% 0.18/0.36  # Generated clauses                    : 71
% 0.18/0.36  # ...of the previous two non-trivial   : 70
% 0.18/0.36  # Contextual simplify-reflections      : 0
% 0.18/0.36  # Paramodulations                      : 69
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 2
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 40
% 0.18/0.36  #    Positive orientable unit clauses  : 13
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 3
% 0.18/0.36  #    Non-unit-clauses                  : 24
% 0.18/0.36  # Current number of unprocessed clauses: 38
% 0.18/0.36  # ...number of literals in the above   : 132
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 27
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 140
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 110
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 5
% 0.18/0.36  # Unit Clause-clause subsumption calls : 21
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 2
% 0.18/0.36  # BW rewrite match successes           : 2
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 3180
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.030 s
% 0.18/0.36  # System time              : 0.004 s
% 0.18/0.36  # Total time               : 0.035 s
% 0.18/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
