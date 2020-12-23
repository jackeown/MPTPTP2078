%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:40 EST 2020

% Result     : Theorem 1.25s
% Output     : CNFRefutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   95 (1207 expanded)
%              Number of clauses        :   64 ( 567 expanded)
%              Number of leaves         :   15 ( 306 expanded)
%              Depth                    :   15
%              Number of atoms          :  199 (2633 expanded)
%              Number of equality atoms :   46 ( 807 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r1_tarski(X2,X3)
          <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t33_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_16,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(X12,X13)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

fof(c_0_17,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_18,plain,(
    ! [X26,X27] :
      ( ( ~ r1_xboole_0(X26,X27)
        | k4_xboole_0(X26,X27) = X26 )
      & ( k4_xboole_0(X26,X27) != X26
        | r1_xboole_0(X26,X27) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_19,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X30,X29)
        | r1_tarski(X30,X28)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r1_tarski(X31,X28)
        | r2_hidden(X31,X29)
        | X29 != k1_zfmisc_1(X28) )
      & ( ~ r2_hidden(esk1_2(X32,X33),X33)
        | ~ r1_tarski(esk1_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) )
      & ( r2_hidden(esk1_2(X32,X33),X33)
        | r1_tarski(esk1_2(X32,X33),X32)
        | X33 = k1_zfmisc_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_20,plain,(
    ! [X35,X36] :
      ( ( ~ m1_subset_1(X36,X35)
        | r2_hidden(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ r2_hidden(X36,X35)
        | m1_subset_1(X36,X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X36,X35)
        | v1_xboole_0(X36)
        | ~ v1_xboole_0(X35) )
      & ( ~ v1_xboole_0(X36)
        | m1_subset_1(X36,X35)
        | ~ v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_22,plain,(
    ! [X39] : ~ v1_xboole_0(k1_zfmisc_1(X39)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_23,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_31,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_25]),c_0_25])).

cnf(c_0_39,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_41,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X7)
      | r1_xboole_0(X7,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | k3_subset_1(X37,X38) = k4_xboole_0(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_44,plain,(
    ! [X18,X19,X20] :
      ( ~ r1_tarski(X18,X19)
      | r1_tarski(k4_xboole_0(X18,X20),k4_xboole_0(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( r1_xboole_0(esk4_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_42])).

fof(c_0_49,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_50,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_51,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_52,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk4_0,X1) = esk4_0
    | ~ r1_xboole_0(esk2_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_25])).

cnf(c_0_61,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X3)),k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_25]),c_0_25])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_54]),c_0_30])).

cnf(c_0_63,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_38])).

cnf(c_0_64,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_66,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_59,c_0_25])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_61,c_0_34])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_62])).

cnf(c_0_71,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_subset_1(X1,k3_xboole_0(X1,X2))
    | ~ m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_64]),c_0_29])])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_65]),c_0_66])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_54])])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = k3_subset_1(esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_64]),c_0_29])]),c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0)) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_64]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_74])).

cnf(c_0_79,plain,
    ( r1_xboole_0(k5_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_65])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_72]),c_0_40])])).

cnf(c_0_82,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(esk3_0,X1)
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r1_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( k3_xboole_0(esk3_0,X1) = esk3_0
    | ~ r1_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_82])).

cnf(c_0_86,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_60])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_56]),c_0_57])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_90,plain,
    ( r1_tarski(k3_subset_1(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(k3_subset_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_69,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_88]),c_0_54])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_80])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_88]),c_0_92]),c_0_29])]),c_0_93]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.25/1.50  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.25/1.50  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.25/1.50  #
% 1.25/1.50  # Preprocessing time       : 0.028 s
% 1.25/1.50  # Presaturation interreduction done
% 1.25/1.50  
% 1.25/1.50  # Proof found!
% 1.25/1.50  # SZS status Theorem
% 1.25/1.50  # SZS output start CNFRefutation
% 1.25/1.50  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 1.25/1.50  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.25/1.50  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.25/1.50  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.25/1.50  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.25/1.50  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.25/1.50  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.25/1.50  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.25/1.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.25/1.50  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.25/1.50  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.25/1.50  fof(t33_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 1.25/1.50  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.25/1.50  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.25/1.50  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.25/1.50  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 1.25/1.50  fof(c_0_16, plain, ![X12, X13, X14]:((r1_tarski(X12,X13)|~r1_tarski(X12,k4_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_tarski(X12,k4_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 1.25/1.50  fof(c_0_17, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 1.25/1.50  fof(c_0_18, plain, ![X26, X27]:((~r1_xboole_0(X26,X27)|k4_xboole_0(X26,X27)=X26)&(k4_xboole_0(X26,X27)!=X26|r1_xboole_0(X26,X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 1.25/1.50  fof(c_0_19, plain, ![X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X30,X29)|r1_tarski(X30,X28)|X29!=k1_zfmisc_1(X28))&(~r1_tarski(X31,X28)|r2_hidden(X31,X29)|X29!=k1_zfmisc_1(X28)))&((~r2_hidden(esk1_2(X32,X33),X33)|~r1_tarski(esk1_2(X32,X33),X32)|X33=k1_zfmisc_1(X32))&(r2_hidden(esk1_2(X32,X33),X33)|r1_tarski(esk1_2(X32,X33),X32)|X33=k1_zfmisc_1(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 1.25/1.50  fof(c_0_20, plain, ![X35, X36]:(((~m1_subset_1(X36,X35)|r2_hidden(X36,X35)|v1_xboole_0(X35))&(~r2_hidden(X36,X35)|m1_subset_1(X36,X35)|v1_xboole_0(X35)))&((~m1_subset_1(X36,X35)|v1_xboole_0(X36)|~v1_xboole_0(X35))&(~v1_xboole_0(X36)|m1_subset_1(X36,X35)|~v1_xboole_0(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 1.25/1.50  fof(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 1.25/1.50  fof(c_0_22, plain, ![X39]:~v1_xboole_0(k1_zfmisc_1(X39)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 1.25/1.50  fof(c_0_23, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 1.25/1.50  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.25/1.50  cnf(c_0_25, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.25/1.50  cnf(c_0_26, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.25/1.50  cnf(c_0_27, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.25/1.50  cnf(c_0_28, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.25/1.50  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.25/1.50  cnf(c_0_30, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.25/1.50  fof(c_0_31, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.25/1.50  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.25/1.50  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 1.25/1.50  cnf(c_0_34, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 1.25/1.50  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_27])).
% 1.25/1.50  cnf(c_0_36, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 1.25/1.50  cnf(c_0_37, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.25/1.50  cnf(c_0_38, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_25]), c_0_25])).
% 1.25/1.50  cnf(c_0_39, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.25/1.50  cnf(c_0_40, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.25/1.50  fof(c_0_41, plain, ![X6, X7]:(~r1_xboole_0(X6,X7)|r1_xboole_0(X7,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 1.25/1.50  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_37])).
% 1.25/1.50  fof(c_0_43, plain, ![X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(X37))|k3_subset_1(X37,X38)=k4_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 1.25/1.50  fof(c_0_44, plain, ![X18, X19, X20]:(~r1_tarski(X18,X19)|r1_tarski(k4_xboole_0(X18,X20),k4_xboole_0(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_xboole_1])])).
% 1.25/1.50  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 1.25/1.50  cnf(c_0_46, negated_conjecture, (r1_xboole_0(esk4_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.25/1.50  cnf(c_0_47, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.25/1.50  cnf(c_0_48, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_33, c_0_42])).
% 1.25/1.50  fof(c_0_49, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 1.25/1.50  fof(c_0_50, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 1.25/1.50  fof(c_0_51, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 1.25/1.50  cnf(c_0_52, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.25/1.50  cnf(c_0_53, plain, (r1_tarski(k4_xboole_0(X1,X3),k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.25/1.50  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.25/1.50  cnf(c_0_55, negated_conjecture, (k3_xboole_0(esk4_0,X1)=esk4_0|~r1_xboole_0(esk2_0,k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.25/1.50  cnf(c_0_56, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.25/1.50  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 1.25/1.50  cnf(c_0_58, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.25/1.50  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.25/1.50  cnf(c_0_60, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_52, c_0_25])).
% 1.25/1.50  cnf(c_0_61, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X3)),k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_25]), c_0_25])).
% 1.25/1.50  cnf(c_0_62, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_54]), c_0_30])).
% 1.25/1.50  cnf(c_0_63, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_38])).
% 1.25/1.50  cnf(c_0_64, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 1.25/1.50  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_58, c_0_57])).
% 1.25/1.50  cnf(c_0_66, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_59, c_0_25])).
% 1.25/1.50  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_33, c_0_60])).
% 1.25/1.50  cnf(c_0_68, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.25/1.50  cnf(c_0_69, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_61, c_0_34])).
% 1.25/1.50  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_62])).
% 1.25/1.50  cnf(c_0_71, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_subset_1(X1,k3_xboole_0(X1,X2))|~m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_60, c_0_63])).
% 1.25/1.50  cnf(c_0_72, negated_conjecture, (k5_xboole_0(esk2_0,esk4_0)=k3_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_64]), c_0_29])])).
% 1.25/1.50  cnf(c_0_73, plain, (k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_65]), c_0_66])])).
% 1.25/1.50  cnf(c_0_74, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_54])])).
% 1.25/1.50  cnf(c_0_75, negated_conjecture, (r1_tarski(esk3_0,k5_xboole_0(esk2_0,k3_xboole_0(esk2_0,X1)))|~r1_xboole_0(esk3_0,X1)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 1.25/1.50  cnf(c_0_76, negated_conjecture, (k3_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=k3_subset_1(esk2_0,esk4_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_64]), c_0_29])]), c_0_72])).
% 1.25/1.50  cnf(c_0_77, negated_conjecture, (k5_xboole_0(esk2_0,k3_subset_1(esk2_0,esk4_0))=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_64]), c_0_72])).
% 1.25/1.50  cnf(c_0_78, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_74])).
% 1.25/1.50  cnf(c_0_79, plain, (r1_xboole_0(k5_xboole_0(X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_48, c_0_65])).
% 1.25/1.50  cnf(c_0_80, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78])).
% 1.25/1.50  cnf(c_0_81, negated_conjecture, (r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_72]), c_0_40])])).
% 1.25/1.50  cnf(c_0_82, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(esk2_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_70])).
% 1.25/1.50  cnf(c_0_83, negated_conjecture, (r1_xboole_0(esk3_0,X1)|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_80])).
% 1.25/1.50  cnf(c_0_84, negated_conjecture, (r1_xboole_0(esk4_0,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_81])).
% 1.25/1.50  cnf(c_0_85, negated_conjecture, (k3_xboole_0(esk3_0,X1)=esk3_0|~r1_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)))), inference(spm,[status(thm)],[c_0_45, c_0_82])).
% 1.25/1.50  cnf(c_0_86, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_66, c_0_60])).
% 1.25/1.50  cnf(c_0_87, negated_conjecture, (r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.25/1.50  cnf(c_0_88, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_56]), c_0_57])).
% 1.25/1.50  cnf(c_0_89, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.25/1.50  cnf(c_0_90, plain, (r1_tarski(k3_subset_1(X1,X2),k5_xboole_0(X1,k3_xboole_0(X1,X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_xboole_0(k3_subset_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_69, c_0_86])).
% 1.25/1.50  cnf(c_0_91, negated_conjecture, (r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_87])).
% 1.25/1.50  cnf(c_0_92, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_88]), c_0_54])])).
% 1.25/1.50  cnf(c_0_93, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_80])])).
% 1.25/1.50  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_88]), c_0_92]), c_0_29])]), c_0_93]), ['proof']).
% 1.25/1.50  # SZS output end CNFRefutation
% 1.25/1.50  # Proof object total steps             : 95
% 1.25/1.50  # Proof object clause steps            : 64
% 1.25/1.50  # Proof object formula steps           : 31
% 1.25/1.50  # Proof object conjectures             : 32
% 1.25/1.50  # Proof object clause conjectures      : 29
% 1.25/1.50  # Proof object formula conjectures     : 3
% 1.25/1.50  # Proof object initial clauses used    : 18
% 1.25/1.50  # Proof object initial formulas used   : 15
% 1.25/1.50  # Proof object generating inferences   : 37
% 1.25/1.50  # Proof object simplifying inferences  : 37
% 1.25/1.50  # Training examples: 0 positive, 0 negative
% 1.25/1.50  # Parsed axioms                        : 18
% 1.25/1.50  # Removed by relevancy pruning/SinE    : 0
% 1.25/1.50  # Initial clauses                      : 31
% 1.25/1.50  # Removed in clause preprocessing      : 1
% 1.25/1.50  # Initial clauses in saturation        : 30
% 1.25/1.50  # Processed clauses                    : 15055
% 1.25/1.50  # ...of these trivial                  : 355
% 1.25/1.50  # ...subsumed                          : 12517
% 1.25/1.50  # ...remaining for further processing  : 2183
% 1.25/1.50  # Other redundant clauses eliminated   : 329
% 1.25/1.50  # Clauses deleted for lack of memory   : 0
% 1.25/1.50  # Backward-subsumed                    : 428
% 1.25/1.50  # Backward-rewritten                   : 150
% 1.25/1.50  # Generated clauses                    : 140991
% 1.25/1.50  # ...of the previous two non-trivial   : 123027
% 1.25/1.50  # Contextual simplify-reflections      : 58
% 1.25/1.50  # Paramodulations                      : 140604
% 1.25/1.50  # Factorizations                       : 58
% 1.25/1.50  # Equation resolutions                 : 329
% 1.25/1.50  # Propositional unsat checks           : 0
% 1.25/1.50  #    Propositional check models        : 0
% 1.25/1.50  #    Propositional check unsatisfiable : 0
% 1.25/1.50  #    Propositional clauses             : 0
% 1.25/1.50  #    Propositional clauses after purity: 0
% 1.25/1.50  #    Propositional unsat core size     : 0
% 1.25/1.50  #    Propositional preprocessing time  : 0.000
% 1.25/1.50  #    Propositional encoding time       : 0.000
% 1.25/1.50  #    Propositional solver time         : 0.000
% 1.25/1.50  #    Success case prop preproc time    : 0.000
% 1.25/1.50  #    Success case prop encoding time   : 0.000
% 1.25/1.50  #    Success case prop solver time     : 0.000
% 1.25/1.50  # Current number of processed clauses  : 1571
% 1.25/1.50  #    Positive orientable unit clauses  : 125
% 1.25/1.50  #    Positive unorientable unit clauses: 2
% 1.25/1.50  #    Negative unit clauses             : 50
% 1.25/1.50  #    Non-unit-clauses                  : 1394
% 1.25/1.50  # Current number of unprocessed clauses: 106509
% 1.25/1.50  # ...number of literals in the above   : 361700
% 1.25/1.50  # Current number of archived formulas  : 0
% 1.25/1.50  # Current number of archived clauses   : 608
% 1.25/1.50  # Clause-clause subsumption calls (NU) : 282559
% 1.25/1.50  # Rec. Clause-clause subsumption calls : 208520
% 1.25/1.50  # Non-unit clause-clause subsumptions  : 8896
% 1.25/1.50  # Unit Clause-clause subsumption calls : 20102
% 1.25/1.50  # Rewrite failures with RHS unbound    : 6
% 1.25/1.50  # BW rewrite match attempts            : 516
% 1.25/1.50  # BW rewrite match successes           : 48
% 1.25/1.50  # Condensation attempts                : 0
% 1.25/1.50  # Condensation successes               : 0
% 1.25/1.50  # Termbank termtop insertions          : 1920090
% 1.25/1.51  
% 1.25/1.51  # -------------------------------------------------
% 1.25/1.51  # User time                : 1.096 s
% 1.25/1.51  # System time              : 0.047 s
% 1.25/1.51  # Total time               : 1.144 s
% 1.25/1.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
