%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:37 EST 2020

% Result     : Theorem 38.46s
% Output     : CNFRefutation 38.46s
% Verified   : 
% Statistics : Number of formulae       :  218 (9478445 expanded)
%              Number of clauses        :  181 (4500575 expanded)
%              Number of leaves         :   18 (2430584 expanded)
%              Depth                    :   47
%              Number of atoms          :  394 (19300879 expanded)
%              Number of equality atoms :   94 (6988112 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

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

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_19,plain,(
    ! [X29,X30] : k4_xboole_0(X29,k4_xboole_0(X29,X30)) = k3_xboole_0(X29,X30) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_21,plain,(
    ! [X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X36,X35)
        | r1_tarski(X36,X34)
        | X35 != k1_zfmisc_1(X34) )
      & ( ~ r1_tarski(X37,X34)
        | r2_hidden(X37,X35)
        | X35 != k1_zfmisc_1(X34) )
      & ( ~ r2_hidden(esk1_2(X38,X39),X39)
        | ~ r1_tarski(esk1_2(X38,X39),X38)
        | X39 = k1_zfmisc_1(X38) )
      & ( r2_hidden(esk1_2(X38,X39),X39)
        | r1_tarski(esk1_2(X38,X39),X38)
        | X39 = k1_zfmisc_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_22,plain,(
    ! [X41,X42] :
      ( ( ~ m1_subset_1(X42,X41)
        | r2_hidden(X42,X41)
        | v1_xboole_0(X41) )
      & ( ~ r2_hidden(X42,X41)
        | m1_subset_1(X42,X41)
        | v1_xboole_0(X41) )
      & ( ~ m1_subset_1(X42,X41)
        | v1_xboole_0(X42)
        | ~ v1_xboole_0(X41) )
      & ( ~ v1_xboole_0(X42)
        | m1_subset_1(X42,X41)
        | ~ v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_24,plain,(
    ! [X45] : ~ v1_xboole_0(k1_zfmisc_1(X45)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_25,plain,(
    ! [X22,X23] : r1_tarski(k4_xboole_0(X22,X23),X22) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X20,X21] :
      ( ~ r1_tarski(X20,X21)
      | k3_xboole_0(X20,X21) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_35,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(k2_xboole_0(X15,X16),X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_38,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

fof(c_0_41,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_42,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_28])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_46,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1))) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_38])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_45]),c_0_33])).

fof(c_0_52,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(X12,X13)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_53,plain,
    ( k5_xboole_0(X1,X1) = k3_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_54,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_48])).

cnf(c_0_56,plain,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)) = k5_xboole_0(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_44])])).

cnf(c_0_61,negated_conjecture,
    ( k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_57])).

fof(c_0_63,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,k2_xboole_0(X32,X33))
      | ~ r1_xboole_0(X31,X33)
      | r1_tarski(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

fof(c_0_64,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_60]),c_0_61]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_62]),c_0_44])])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_55]),c_0_56])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_67]),c_0_67]),c_0_68]),c_0_68])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk4_0,esk4_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_44])).

cnf(c_0_76,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_37])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_72])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_73,c_0_28])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_56])])).

cnf(c_0_80,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_76,c_0_48])).

cnf(c_0_81,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_44])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_37])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),k3_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

fof(c_0_84,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | k3_subset_1(X43,X44) = k4_xboole_0(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_81]),c_0_56])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_90,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),k5_xboole_0(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_88,c_0_28])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_33])).

fof(c_0_95,plain,(
    ! [X24,X25] : k2_xboole_0(X24,k4_xboole_0(X25,X24)) = k2_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_96,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_42])).

cnf(c_0_97,negated_conjecture,
    ( k5_xboole_0(esk4_0,esk4_0) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_87])])).

cnf(c_0_98,plain,
    ( k5_xboole_0(X1,X2) = k3_subset_1(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_55]),c_0_94])).

fof(c_0_99,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_100,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_37])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,esk3_0),X1) ),
    inference(rw,[status(thm)],[c_0_87,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( k5_xboole_0(esk3_0,esk3_0) = k3_subset_1(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_44])])).

cnf(c_0_104,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_105,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_100,c_0_28])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,esk3_0),X1) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_107,negated_conjecture,
    ( k3_subset_1(esk4_0,esk4_0) = k3_subset_1(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_103]),c_0_44])])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_70])).

cnf(c_0_109,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_104])).

cnf(c_0_110,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_105,c_0_48])).

cnf(c_0_111,negated_conjecture,
    ( k3_xboole_0(X1,k5_xboole_0(esk3_0,esk3_0)) = k5_xboole_0(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( k3_xboole_0(k3_subset_1(esk3_0,esk3_0),X1) = k3_subset_1(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_103]),c_0_103]),c_0_107]),c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_47])).

cnf(c_0_114,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_115,negated_conjecture,
    ( k3_xboole_0(X1,k3_subset_1(esk3_0,esk3_0)) = k3_subset_1(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_103]),c_0_103]),c_0_107]),c_0_107])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(k3_subset_1(esk3_0,esk3_0),k3_subset_1(esk3_0,esk3_0)) = k3_subset_1(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_112]),c_0_112])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk3_0,esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103]),c_0_107])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_42])).

cnf(c_0_119,negated_conjecture,
    ( k2_xboole_0(X1,k3_subset_1(esk3_0,esk3_0)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116]),c_0_117])])).

fof(c_0_120,plain,(
    ! [X26,X27,X28] :
      ( ~ r1_tarski(k4_xboole_0(X26,X27),X28)
      | r1_tarski(X26,k2_xboole_0(X27,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(X1,esk4_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_48])).

cnf(c_0_122,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_105])).

cnf(c_0_123,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(esk3_0,esk3_0),X1) = X1 ),
    inference(spm,[status(thm)],[c_0_104,c_0_119])).

cnf(c_0_124,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_125,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_109])).

cnf(c_0_126,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,X1),esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_121,c_0_38])).

cnf(c_0_127,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k2_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_59]),c_0_104])).

cnf(c_0_128,negated_conjecture,
    ( k5_xboole_0(X1,k3_subset_1(esk3_0,esk3_0)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_123]),c_0_115]),c_0_123])).

cnf(c_0_129,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) ),
    inference(rw,[status(thm)],[c_0_124,c_0_28])).

cnf(c_0_130,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_104])).

cnf(c_0_131,negated_conjecture,
    ( k2_xboole_0(esk2_0,esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_76])])).

cnf(c_0_132,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_44])).

cnf(c_0_133,negated_conjecture,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_115]),c_0_128]),c_0_119]),c_0_128]),c_0_117])])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(esk4_0,k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_118])).

cnf(c_0_135,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_136,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(X1,X1),X1) ),
    inference(spm,[status(thm)],[c_0_132,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(X2,esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk2_0,esk2_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_56])])).

cnf(c_0_139,negated_conjecture,
    ( X1 = k5_xboole_0(esk3_0,esk3_0)
    | ~ r1_tarski(X1,k5_xboole_0(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_102])).

cnf(c_0_140,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_137])).

cnf(c_0_141,negated_conjecture,
    ( r1_xboole_0(k3_subset_1(X1,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_98]),c_0_44])])).

cnf(c_0_142,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_98]),c_0_44])])).

cnf(c_0_143,negated_conjecture,
    ( X1 = k3_subset_1(esk3_0,esk3_0)
    | ~ r1_tarski(X1,k3_subset_1(esk3_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_103]),c_0_103]),c_0_107]),c_0_107])).

cnf(c_0_144,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_141]),c_0_142])])).

cnf(c_0_145,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,X2))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

cnf(c_0_146,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_57])).

cnf(c_0_147,negated_conjecture,
    ( k3_subset_1(esk3_0,esk3_0) = k3_subset_1(esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_148,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(esk3_0,esk3_0))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_128]),c_0_117])])).

cnf(c_0_149,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_146,c_0_42])).

cnf(c_0_151,plain,
    ( k2_xboole_0(X1,k5_xboole_0(X2,X2)) = k2_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_38])).

cnf(c_0_152,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2))) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_55])).

cnf(c_0_153,negated_conjecture,
    ( k5_xboole_0(X1,k3_subset_1(esk2_0,esk2_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_128,c_0_147])).

cnf(c_0_154,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_148,c_0_149])).

cnf(c_0_155,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_150])).

cnf(c_0_156,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,k5_xboole_0(X3,X3))
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_151])).

cnf(c_0_157,negated_conjecture,
    ( k5_xboole_0(X1,X1) = k3_subset_1(esk2_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_133]),c_0_144])])).

cnf(c_0_158,negated_conjecture,
    ( r1_xboole_0(X1,k3_subset_1(esk2_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_154,c_0_147])).

cnf(c_0_159,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_155,c_0_109])).

cnf(c_0_160,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(k3_subset_1(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_129,c_0_93])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_162,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_156,c_0_157]),c_0_158])])).

cnf(c_0_163,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | ~ r1_xboole_0(esk3_0,X2)
    | ~ r1_tarski(esk2_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_159])).

cnf(c_0_164,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_32])])).

cnf(c_0_165,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_37])).

cnf(c_0_166,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_162,c_0_104])).

cnf(c_0_167,plain,
    ( r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_108,c_0_149])).

cnf(c_0_168,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_163,c_0_164])).

cnf(c_0_169,plain,
    ( r1_xboole_0(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_165,c_0_93])).

cnf(c_0_170,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X3,X4),X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_166,c_0_167])).

cnf(c_0_171,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_169]),c_0_45])])).

cnf(c_0_172,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_170,c_0_70])).

cnf(c_0_173,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_55]),c_0_44]),c_0_57])])).

cnf(c_0_174,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X2,esk3_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_172,c_0_173])).

cnf(c_0_175,negated_conjecture,
    ( k3_subset_1(esk2_0,esk2_0) = k3_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_157]),c_0_44])])).

cnf(c_0_176,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r1_tarski(X1,k3_xboole_0(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_174,c_0_76])).

cnf(c_0_177,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3))) ),
    inference(spm,[status(thm)],[c_0_129,c_0_50])).

cnf(c_0_178,negated_conjecture,
    ( k2_xboole_0(X1,k3_subset_1(esk2_0,esk2_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_119,c_0_147])).

cnf(c_0_179,negated_conjecture,
    ( k3_subset_1(X1,X1) = k3_subset_1(X2,X2) ),
    inference(spm,[status(thm)],[c_0_175,c_0_175])).

cnf(c_0_180,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_176,c_0_44])).

cnf(c_0_181,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_55]),c_0_76])])).

cnf(c_0_182,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2) ),
    inference(spm,[status(thm)],[c_0_177,c_0_109])).

cnf(c_0_183,negated_conjecture,
    ( k2_xboole_0(X1,k3_subset_1(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_178,c_0_179])).

cnf(c_0_184,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_180,c_0_181])).

cnf(c_0_185,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_182,c_0_183])).

cnf(c_0_186,negated_conjecture,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)),X2)
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_140,c_0_132])).

cnf(c_0_187,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,X1),esk4_0)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_184,c_0_55])).

cnf(c_0_188,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(k5_xboole_0(X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_185,c_0_55])).

cnf(c_0_189,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_187]),c_0_76])]),c_0_48])).

cnf(c_0_190,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2))) = k3_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_93])).

cnf(c_0_191,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_189]),c_0_80])])).

cnf(c_0_192,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X1)
    | ~ r1_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_42])).

cnf(c_0_193,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_48])).

cnf(c_0_194,plain,
    ( r1_tarski(X1,k2_xboole_0(k3_subset_1(X1,X2),k2_xboole_0(k3_xboole_0(X1,X2),X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_177,c_0_190])).

cnf(c_0_195,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_191]),c_0_80])])).

cnf(c_0_196,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X1,X2))),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192,c_0_132]),c_0_48])).

cnf(c_0_197,plain,
    ( r1_tarski(k5_xboole_0(X1,X2),X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_193,c_0_38])).

cnf(c_0_198,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(k3_subset_1(esk2_0,esk3_0),k2_xboole_0(esk3_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_195]),c_0_45])])).

cnf(c_0_199,negated_conjecture,
    ( k2_xboole_0(esk3_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_184]),c_0_104])).

cnf(c_0_200,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X3) ),
    inference(spm,[status(thm)],[c_0_129,c_0_48])).

cnf(c_0_201,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(esk4_0,X1),k3_xboole_0(X1,k2_xboole_0(esk4_0,X1))),esk2_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_196])).

cnf(c_0_202,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_197]),c_0_76])]),c_0_48])).

cnf(c_0_203,negated_conjecture,
    ( r1_tarski(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198,c_0_199]),c_0_104])).

cnf(c_0_204,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk4_0,X1),k2_xboole_0(X1,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_200,c_0_201])).

cnf(c_0_205,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk3_0) = k3_subset_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_195]),c_0_45])])).

cnf(c_0_206,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_202]),c_0_80])])).

cnf(c_0_207,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X2)
    | ~ r1_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X1) ),
    inference(spm,[status(thm)],[c_0_130,c_0_42])).

cnf(c_0_208,negated_conjecture,
    ( k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)) = esk2_0
    | ~ r1_tarski(k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_203])).

cnf(c_0_209,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk4_0,X1),esk2_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_166,c_0_204])).

cnf(c_0_210,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_205]),c_0_57])])).

cnf(c_0_211,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_206]),c_0_80])])).

cnf(c_0_212,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_213,plain,
    ( r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X1,X2))),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207,c_0_132]),c_0_48])).

cnf(c_0_214,negated_conjecture,
    ( k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208,c_0_209]),c_0_210])])).

cnf(c_0_215,negated_conjecture,
    ( k5_xboole_0(esk2_0,esk4_0) = k3_subset_1(esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_211]),c_0_32])])).

cnf(c_0_216,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_212,c_0_173])])).

cnf(c_0_217,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213,c_0_214]),c_0_48]),c_0_211]),c_0_215]),c_0_216]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 38.46/38.65  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 38.46/38.65  # and selection function SelectComplexExceptUniqMaxHorn.
% 38.46/38.65  #
% 38.46/38.65  # Preprocessing time       : 0.044 s
% 38.46/38.65  # Presaturation interreduction done
% 38.46/38.65  
% 38.46/38.65  # Proof found!
% 38.46/38.65  # SZS status Theorem
% 38.46/38.65  # SZS output start CNFRefutation
% 38.46/38.65  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 38.46/38.65  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 38.46/38.65  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 38.46/38.65  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 38.46/38.65  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 38.46/38.65  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 38.46/38.65  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 38.46/38.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 38.46/38.65  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 38.46/38.65  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 38.46/38.65  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 38.46/38.65  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 38.46/38.65  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 38.46/38.65  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 38.46/38.65  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 38.46/38.65  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 38.46/38.65  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 38.46/38.65  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 38.46/38.65  fof(c_0_18, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 38.46/38.65  fof(c_0_19, plain, ![X29, X30]:k4_xboole_0(X29,k4_xboole_0(X29,X30))=k3_xboole_0(X29,X30), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 38.46/38.65  fof(c_0_20, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 38.46/38.65  fof(c_0_21, plain, ![X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X36,X35)|r1_tarski(X36,X34)|X35!=k1_zfmisc_1(X34))&(~r1_tarski(X37,X34)|r2_hidden(X37,X35)|X35!=k1_zfmisc_1(X34)))&((~r2_hidden(esk1_2(X38,X39),X39)|~r1_tarski(esk1_2(X38,X39),X38)|X39=k1_zfmisc_1(X38))&(r2_hidden(esk1_2(X38,X39),X39)|r1_tarski(esk1_2(X38,X39),X38)|X39=k1_zfmisc_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 38.46/38.65  fof(c_0_22, plain, ![X41, X42]:(((~m1_subset_1(X42,X41)|r2_hidden(X42,X41)|v1_xboole_0(X41))&(~r2_hidden(X42,X41)|m1_subset_1(X42,X41)|v1_xboole_0(X41)))&((~m1_subset_1(X42,X41)|v1_xboole_0(X42)|~v1_xboole_0(X41))&(~v1_xboole_0(X42)|m1_subset_1(X42,X41)|~v1_xboole_0(X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 38.46/38.65  fof(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 38.46/38.65  fof(c_0_24, plain, ![X45]:~v1_xboole_0(k1_zfmisc_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 38.46/38.65  fof(c_0_25, plain, ![X22, X23]:r1_tarski(k4_xboole_0(X22,X23),X22), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 38.46/38.65  fof(c_0_26, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 38.46/38.65  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 38.46/38.65  cnf(c_0_28, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 38.46/38.65  fof(c_0_29, plain, ![X20, X21]:(~r1_tarski(X20,X21)|k3_xboole_0(X20,X21)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 38.46/38.65  cnf(c_0_30, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 38.46/38.65  cnf(c_0_31, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 38.46/38.65  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 38.46/38.65  cnf(c_0_33, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 38.46/38.65  cnf(c_0_34, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 38.46/38.65  fof(c_0_35, plain, ![X15, X16, X17]:(~r1_tarski(k2_xboole_0(X15,X16),X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 38.46/38.65  cnf(c_0_36, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 38.46/38.65  cnf(c_0_37, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 38.46/38.65  cnf(c_0_38, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 38.46/38.65  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_30])).
% 38.46/38.65  cnf(c_0_40, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 38.46/38.65  fof(c_0_41, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 38.46/38.65  cnf(c_0_42, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_34, c_0_28])).
% 38.46/38.65  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 38.46/38.65  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_36])).
% 38.46/38.65  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 38.46/38.65  cnf(c_0_46, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X1)))=X1|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 38.46/38.65  cnf(c_0_47, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 38.46/38.65  cnf(c_0_48, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 38.46/38.65  cnf(c_0_49, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_38])).
% 38.46/38.65  cnf(c_0_50, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 38.46/38.65  cnf(c_0_51, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_45]), c_0_33])).
% 38.46/38.65  fof(c_0_52, plain, ![X12, X13, X14]:((r1_tarski(X12,X13)|~r1_tarski(X12,k4_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_tarski(X12,k4_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 38.46/38.65  cnf(c_0_53, plain, (k5_xboole_0(X1,X1)=k3_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 38.46/38.65  cnf(c_0_54, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0)))=esk4_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 38.46/38.65  cnf(c_0_55, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_38, c_0_48])).
% 38.46/38.65  cnf(c_0_56, plain, (r1_tarski(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 38.46/38.65  cnf(c_0_57, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_39, c_0_51])).
% 38.46/38.65  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 38.46/38.65  cnf(c_0_59, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))=k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_37])).
% 38.46/38.65  cnf(c_0_60, negated_conjecture, (k3_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))=k5_xboole_0(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_44])])).
% 38.46/38.65  cnf(c_0_61, negated_conjecture, (k5_xboole_0(esk4_0,k5_xboole_0(esk4_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 38.46/38.65  cnf(c_0_62, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0)))=esk3_0), inference(spm,[status(thm)],[c_0_46, c_0_57])).
% 38.46/38.65  fof(c_0_63, plain, ![X31, X32, X33]:(~r1_tarski(X31,k2_xboole_0(X32,X33))|~r1_xboole_0(X31,X33)|r1_tarski(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 38.46/38.65  fof(c_0_64, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 38.46/38.65  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_58, c_0_28])).
% 38.46/38.65  cnf(c_0_66, negated_conjecture, (k3_xboole_0(esk4_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_60]), c_0_61]), c_0_61])).
% 38.46/38.65  cnf(c_0_67, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))=k5_xboole_0(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_62]), c_0_44])])).
% 38.46/38.65  cnf(c_0_68, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk3_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_55]), c_0_56])])).
% 38.46/38.65  cnf(c_0_69, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 38.46/38.65  cnf(c_0_70, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 38.46/38.65  cnf(c_0_71, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 38.46/38.65  cnf(c_0_72, negated_conjecture, (k3_xboole_0(esk3_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_67]), c_0_67]), c_0_68]), c_0_68])).
% 38.46/38.65  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 38.46/38.65  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 38.46/38.65  cnf(c_0_75, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk4_0,esk4_0),esk4_0)), inference(spm,[status(thm)],[c_0_71, c_0_44])).
% 38.46/38.65  cnf(c_0_76, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_42, c_0_37])).
% 38.46/38.65  cnf(c_0_77, negated_conjecture, (r1_xboole_0(X1,esk3_0)|~r1_tarski(X1,k5_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_72])).
% 38.46/38.65  cnf(c_0_78, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_73, c_0_28])).
% 38.46/38.65  cnf(c_0_79, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1)|~r1_tarski(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_56])])).
% 38.46/38.65  cnf(c_0_80, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_76, c_0_48])).
% 38.46/38.65  cnf(c_0_81, negated_conjecture, (r1_xboole_0(k5_xboole_0(esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_77, c_0_44])).
% 38.46/38.65  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_78, c_0_37])).
% 38.46/38.65  cnf(c_0_83, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),k3_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 38.46/38.65  fof(c_0_84, plain, ![X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|k3_subset_1(X43,X44)=k4_xboole_0(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 38.46/38.65  cnf(c_0_85, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 38.46/38.65  cnf(c_0_86, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),X1)|~r1_tarski(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_81]), c_0_56])])).
% 38.46/38.65  cnf(c_0_87, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 38.46/38.65  cnf(c_0_88, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 38.46/38.65  cnf(c_0_89, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 38.46/38.65  cnf(c_0_90, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_85])).
% 38.46/38.65  cnf(c_0_91, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 38.46/38.65  cnf(c_0_92, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),k5_xboole_0(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 38.46/38.65  cnf(c_0_93, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_88, c_0_28])).
% 38.46/38.65  cnf(c_0_94, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_33])).
% 38.46/38.65  fof(c_0_95, plain, ![X24, X25]:k2_xboole_0(X24,k4_xboole_0(X25,X24))=k2_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 38.46/38.65  cnf(c_0_96, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=X1|~r1_tarski(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_91, c_0_42])).
% 38.46/38.65  cnf(c_0_97, negated_conjecture, (k5_xboole_0(esk4_0,esk4_0)=k5_xboole_0(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_87])])).
% 38.46/38.65  cnf(c_0_98, plain, (k5_xboole_0(X1,X2)=k3_subset_1(X1,X2)|~r1_tarski(X2,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_55]), c_0_94])).
% 38.46/38.65  fof(c_0_99, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 38.46/38.65  cnf(c_0_100, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 38.46/38.65  cnf(c_0_101, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_96, c_0_37])).
% 38.46/38.65  cnf(c_0_102, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,esk3_0),X1)), inference(rw,[status(thm)],[c_0_87, c_0_97])).
% 38.46/38.65  cnf(c_0_103, negated_conjecture, (k5_xboole_0(esk3_0,esk3_0)=k3_subset_1(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_44])])).
% 38.46/38.65  cnf(c_0_104, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 38.46/38.65  cnf(c_0_105, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_100, c_0_28])).
% 38.46/38.65  cnf(c_0_106, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,esk3_0),X1)=k5_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 38.46/38.65  cnf(c_0_107, negated_conjecture, (k3_subset_1(esk4_0,esk4_0)=k3_subset_1(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_103]), c_0_44])])).
% 38.46/38.65  cnf(c_0_108, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_43, c_0_70])).
% 38.46/38.65  cnf(c_0_109, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_104])).
% 38.46/38.65  cnf(c_0_110, plain, (k2_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_105, c_0_48])).
% 38.46/38.65  cnf(c_0_111, negated_conjecture, (k3_xboole_0(X1,k5_xboole_0(esk3_0,esk3_0))=k5_xboole_0(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_48, c_0_106])).
% 38.46/38.65  cnf(c_0_112, negated_conjecture, (k3_xboole_0(k3_subset_1(esk3_0,esk3_0),X1)=k3_subset_1(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_103]), c_0_103]), c_0_107]), c_0_107])).
% 38.46/38.65  cnf(c_0_113, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_108, c_0_47])).
% 38.46/38.65  cnf(c_0_114, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k5_xboole_0(X2,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 38.46/38.65  cnf(c_0_115, negated_conjecture, (k3_xboole_0(X1,k3_subset_1(esk3_0,esk3_0))=k3_subset_1(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_103]), c_0_103]), c_0_107]), c_0_107])).
% 38.46/38.65  cnf(c_0_116, negated_conjecture, (k5_xboole_0(k3_subset_1(esk3_0,esk3_0),k3_subset_1(esk3_0,esk3_0))=k3_subset_1(esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_112]), c_0_112])).
% 38.46/38.65  cnf(c_0_117, negated_conjecture, (r1_tarski(k3_subset_1(esk3_0,esk3_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103]), c_0_107])).
% 38.46/38.65  cnf(c_0_118, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_113, c_0_42])).
% 38.46/38.65  cnf(c_0_119, negated_conjecture, (k2_xboole_0(X1,k3_subset_1(esk3_0,esk3_0))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116]), c_0_117])])).
% 38.46/38.65  fof(c_0_120, plain, ![X26, X27, X28]:(~r1_tarski(k4_xboole_0(X26,X27),X28)|r1_tarski(X26,k2_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 38.46/38.65  cnf(c_0_121, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(X1,esk4_0)),esk2_0)), inference(spm,[status(thm)],[c_0_118, c_0_48])).
% 38.46/38.65  cnf(c_0_122, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k2_xboole_0(X2,X1)|~r1_tarski(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_70, c_0_105])).
% 38.46/38.65  cnf(c_0_123, negated_conjecture, (k2_xboole_0(k3_subset_1(esk3_0,esk3_0),X1)=X1), inference(spm,[status(thm)],[c_0_104, c_0_119])).
% 38.46/38.65  cnf(c_0_124, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_120])).
% 38.46/38.65  cnf(c_0_125, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_105, c_0_109])).
% 38.46/38.65  cnf(c_0_126, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,X1),esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_121, c_0_38])).
% 38.46/38.65  cnf(c_0_127, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k2_xboole_0(X1,k3_xboole_0(X1,X2))|~r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_59]), c_0_104])).
% 38.46/38.65  cnf(c_0_128, negated_conjecture, (k5_xboole_0(X1,k3_subset_1(esk3_0,esk3_0))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_123]), c_0_115]), c_0_123])).
% 38.46/38.65  cnf(c_0_129, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)), inference(rw,[status(thm)],[c_0_124, c_0_28])).
% 38.46/38.65  cnf(c_0_130, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k2_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_69, c_0_104])).
% 38.46/38.65  cnf(c_0_131, negated_conjecture, (k2_xboole_0(esk2_0,esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_76])])).
% 38.46/38.65  cnf(c_0_132, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_65, c_0_44])).
% 38.46/38.65  cnf(c_0_133, negated_conjecture, (k3_xboole_0(X1,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_115]), c_0_128]), c_0_119]), c_0_128]), c_0_117])])).
% 38.46/38.65  cnf(c_0_134, negated_conjecture, (r1_tarski(esk4_0,k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_129, c_0_118])).
% 38.46/38.65  cnf(c_0_135, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_xboole_0(X1,esk2_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 38.46/38.65  cnf(c_0_136, negated_conjecture, (r1_xboole_0(k5_xboole_0(X1,X1),X1)), inference(spm,[status(thm)],[c_0_132, c_0_133])).
% 38.46/38.65  cnf(c_0_137, negated_conjecture, (r1_tarski(X1,k2_xboole_0(X2,esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_108, c_0_134])).
% 38.46/38.65  cnf(c_0_138, negated_conjecture, (r1_tarski(k5_xboole_0(esk2_0,esk2_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_56])])).
% 38.46/38.65  cnf(c_0_139, negated_conjecture, (X1=k5_xboole_0(esk3_0,esk3_0)|~r1_tarski(X1,k5_xboole_0(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_91, c_0_102])).
% 38.46/38.65  cnf(c_0_140, negated_conjecture, (r1_tarski(X1,X2)|~r1_xboole_0(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_69, c_0_137])).
% 38.46/38.65  cnf(c_0_141, negated_conjecture, (r1_xboole_0(k3_subset_1(X1,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_98]), c_0_44])])).
% 38.46/38.65  cnf(c_0_142, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138, c_0_98]), c_0_44])])).
% 38.46/38.65  cnf(c_0_143, negated_conjecture, (X1=k3_subset_1(esk3_0,esk3_0)|~r1_tarski(X1,k3_subset_1(esk3_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_103]), c_0_103]), c_0_107]), c_0_107])).
% 38.46/38.65  cnf(c_0_144, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_141]), c_0_142])])).
% 38.46/38.65  cnf(c_0_145, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,X2))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_65, c_0_55])).
% 38.46/38.65  cnf(c_0_146, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_108, c_0_57])).
% 38.46/38.65  cnf(c_0_147, negated_conjecture, (k3_subset_1(esk3_0,esk3_0)=k3_subset_1(esk2_0,esk2_0)), inference(spm,[status(thm)],[c_0_143, c_0_144])).
% 38.46/38.65  cnf(c_0_148, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(esk3_0,esk3_0))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_128]), c_0_117])])).
% 38.46/38.65  cnf(c_0_149, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X1,X2),X3))), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 38.46/38.65  cnf(c_0_150, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_146, c_0_42])).
% 38.46/38.65  cnf(c_0_151, plain, (k2_xboole_0(X1,k5_xboole_0(X2,X2))=k2_xboole_0(X1,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_105, c_0_38])).
% 38.46/38.65  cnf(c_0_152, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2)))=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_55])).
% 38.46/38.65  cnf(c_0_153, negated_conjecture, (k5_xboole_0(X1,k3_subset_1(esk2_0,esk2_0))=X1), inference(rw,[status(thm)],[c_0_128, c_0_147])).
% 38.46/38.65  cnf(c_0_154, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_148, c_0_149])).
% 38.46/38.65  cnf(c_0_155, negated_conjecture, (r1_tarski(esk3_0,k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_129, c_0_150])).
% 38.46/38.65  cnf(c_0_156, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,k5_xboole_0(X3,X3))|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_69, c_0_151])).
% 38.46/38.65  cnf(c_0_157, negated_conjecture, (k5_xboole_0(X1,X1)=k3_subset_1(esk2_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_133]), c_0_144])])).
% 38.46/38.65  cnf(c_0_158, negated_conjecture, (r1_xboole_0(X1,k3_subset_1(esk2_0,esk2_0))), inference(rw,[status(thm)],[c_0_154, c_0_147])).
% 38.46/38.65  cnf(c_0_159, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_155, c_0_109])).
% 38.46/38.65  cnf(c_0_160, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(k3_subset_1(X1,X2),X3)), inference(spm,[status(thm)],[c_0_129, c_0_93])).
% 38.46/38.65  cnf(c_0_161, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 38.46/38.65  cnf(c_0_162, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(X3,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_156, c_0_157]), c_0_158])])).
% 38.46/38.65  cnf(c_0_163, negated_conjecture, (r1_tarski(esk3_0,X1)|~r1_xboole_0(esk3_0,X2)|~r1_tarski(esk2_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_69, c_0_159])).
% 38.46/38.65  cnf(c_0_164, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)))|r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_32])])).
% 38.46/38.65  cnf(c_0_165, plain, (r1_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_65, c_0_37])).
% 38.46/38.65  cnf(c_0_166, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_162, c_0_104])).
% 38.46/38.65  cnf(c_0_167, plain, (r1_tarski(X1,k2_xboole_0(k2_xboole_0(X2,X3),X4))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_108, c_0_149])).
% 38.46/38.65  cnf(c_0_168, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_163, c_0_164])).
% 38.46/38.65  cnf(c_0_169, plain, (r1_xboole_0(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_165, c_0_93])).
% 38.46/38.65  cnf(c_0_170, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(X3,X4),X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_166, c_0_167])).
% 38.46/38.65  cnf(c_0_171, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|~r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_169]), c_0_45])])).
% 38.46/38.65  cnf(c_0_172, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_170, c_0_70])).
% 38.46/38.65  cnf(c_0_173, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_55]), c_0_44]), c_0_57])])).
% 38.46/38.65  cnf(c_0_174, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X2,esk3_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_172, c_0_173])).
% 38.46/38.65  cnf(c_0_175, negated_conjecture, (k3_subset_1(esk2_0,esk2_0)=k3_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_157]), c_0_44])])).
% 38.46/38.65  cnf(c_0_176, negated_conjecture, (r1_tarski(X1,esk4_0)|~r1_tarski(X1,k3_xboole_0(esk3_0,X2))), inference(spm,[status(thm)],[c_0_174, c_0_76])).
% 38.46/38.65  cnf(c_0_177, plain, (r1_tarski(X1,k2_xboole_0(X2,k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)))), inference(spm,[status(thm)],[c_0_129, c_0_50])).
% 38.46/38.65  cnf(c_0_178, negated_conjecture, (k2_xboole_0(X1,k3_subset_1(esk2_0,esk2_0))=X1), inference(rw,[status(thm)],[c_0_119, c_0_147])).
% 38.46/38.65  cnf(c_0_179, negated_conjecture, (k3_subset_1(X1,X1)=k3_subset_1(X2,X2)), inference(spm,[status(thm)],[c_0_175, c_0_175])).
% 38.46/38.65  cnf(c_0_180, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_176, c_0_44])).
% 38.46/38.65  cnf(c_0_181, plain, (k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_55]), c_0_76])])).
% 38.46/38.65  cnf(c_0_182, plain, (r1_tarski(X1,X2)|~r1_tarski(k2_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3),X2)), inference(spm,[status(thm)],[c_0_177, c_0_109])).
% 38.46/38.65  cnf(c_0_183, negated_conjecture, (k2_xboole_0(X1,k3_subset_1(X2,X2))=X1), inference(spm,[status(thm)],[c_0_178, c_0_179])).
% 38.46/38.65  cnf(c_0_184, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,X1)),esk4_0)), inference(spm,[status(thm)],[c_0_180, c_0_181])).
% 38.46/38.65  cnf(c_0_185, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_182, c_0_183])).
% 38.46/38.65  cnf(c_0_186, negated_conjecture, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)),X2)|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,esk2_0)),esk4_0)), inference(spm,[status(thm)],[c_0_140, c_0_132])).
% 38.46/38.65  cnf(c_0_187, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,X1),esk4_0)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_184, c_0_55])).
% 38.46/38.65  cnf(c_0_188, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(k5_xboole_0(X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_185, c_0_55])).
% 38.46/38.65  cnf(c_0_189, negated_conjecture, (r1_tarski(k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,esk3_0)),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_187]), c_0_76])]), c_0_48])).
% 38.46/38.65  cnf(c_0_190, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_subset_1(X1,X2)))=k3_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_93])).
% 38.46/38.65  cnf(c_0_191, negated_conjecture, (r1_tarski(esk3_0,k3_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_189]), c_0_80])])).
% 38.46/38.65  cnf(c_0_192, plain, (r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X1)|~r1_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X2)), inference(spm,[status(thm)],[c_0_69, c_0_42])).
% 38.46/38.65  cnf(c_0_193, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_42, c_0_48])).
% 38.46/38.65  cnf(c_0_194, plain, (r1_tarski(X1,k2_xboole_0(k3_subset_1(X1,X2),k2_xboole_0(k3_xboole_0(X1,X2),X3)))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_177, c_0_190])).
% 38.46/38.65  cnf(c_0_195, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_191]), c_0_80])])).
% 38.46/38.65  cnf(c_0_196, plain, (r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X2,k2_xboole_0(X1,X2))),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_192, c_0_132]), c_0_48])).
% 38.46/38.65  cnf(c_0_197, plain, (r1_tarski(k5_xboole_0(X1,X2),X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_193, c_0_38])).
% 38.46/38.65  cnf(c_0_198, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(k3_subset_1(esk2_0,esk3_0),k2_xboole_0(esk3_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194, c_0_195]), c_0_45])])).
% 38.46/38.65  cnf(c_0_199, negated_conjecture, (k2_xboole_0(esk3_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_184]), c_0_104])).
% 38.46/38.65  cnf(c_0_200, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X3)), inference(spm,[status(thm)],[c_0_129, c_0_48])).
% 38.46/38.65  cnf(c_0_201, negated_conjecture, (r1_tarski(k5_xboole_0(k2_xboole_0(esk4_0,X1),k3_xboole_0(X1,k2_xboole_0(esk4_0,X1))),esk2_0)), inference(spm,[status(thm)],[c_0_113, c_0_196])).
% 38.46/38.65  cnf(c_0_202, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)),X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_186, c_0_197]), c_0_76])]), c_0_48])).
% 38.46/38.65  cnf(c_0_203, negated_conjecture, (r1_tarski(esk2_0,k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_198, c_0_199]), c_0_104])).
% 38.46/38.65  cnf(c_0_204, negated_conjecture, (r1_tarski(k2_xboole_0(esk4_0,X1),k2_xboole_0(X1,esk2_0))), inference(spm,[status(thm)],[c_0_200, c_0_201])).
% 38.46/38.65  cnf(c_0_205, negated_conjecture, (k5_xboole_0(esk2_0,esk3_0)=k3_subset_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_195]), c_0_45])])).
% 38.46/38.65  cnf(c_0_206, negated_conjecture, (r1_tarski(esk4_0,k3_xboole_0(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_188, c_0_202]), c_0_80])])).
% 38.46/38.65  cnf(c_0_207, plain, (r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X2)|~r1_xboole_0(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(k2_xboole_0(X1,X2),X3)),X1)), inference(spm,[status(thm)],[c_0_130, c_0_42])).
% 38.46/38.65  cnf(c_0_208, negated_conjecture, (k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0))=esk2_0|~r1_tarski(k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0)),esk2_0)), inference(spm,[status(thm)],[c_0_91, c_0_203])).
% 38.46/38.65  cnf(c_0_209, negated_conjecture, (r1_tarski(k2_xboole_0(esk4_0,X1),esk2_0)|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_166, c_0_204])).
% 38.46/38.65  cnf(c_0_210, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_197, c_0_205]), c_0_57])])).
% 38.46/38.65  cnf(c_0_211, negated_conjecture, (k3_xboole_0(esk2_0,esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_206]), c_0_80])])).
% 38.46/38.65  cnf(c_0_212, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 38.46/38.65  cnf(c_0_213, plain, (r1_tarski(k5_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k2_xboole_0(X1,X2))),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207, c_0_132]), c_0_48])).
% 38.46/38.65  cnf(c_0_214, negated_conjecture, (k2_xboole_0(esk4_0,k3_subset_1(esk2_0,esk3_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_208, c_0_209]), c_0_210])])).
% 38.46/38.65  cnf(c_0_215, negated_conjecture, (k5_xboole_0(esk2_0,esk4_0)=k3_subset_1(esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_211]), c_0_32])])).
% 38.46/38.65  cnf(c_0_216, negated_conjecture, (~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_212, c_0_173])])).
% 38.46/38.65  cnf(c_0_217, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_213, c_0_214]), c_0_48]), c_0_211]), c_0_215]), c_0_216]), ['proof']).
% 38.46/38.65  # SZS output end CNFRefutation
% 38.46/38.65  # Proof object total steps             : 218
% 38.46/38.65  # Proof object clause steps            : 181
% 38.46/38.65  # Proof object formula steps           : 37
% 38.46/38.65  # Proof object conjectures             : 104
% 38.46/38.65  # Proof object clause conjectures      : 101
% 38.46/38.65  # Proof object formula conjectures     : 3
% 38.46/38.65  # Proof object initial clauses used    : 25
% 38.46/38.65  # Proof object initial formulas used   : 18
% 38.46/38.65  # Proof object generating inferences   : 136
% 38.46/38.65  # Proof object simplifying inferences  : 132
% 38.46/38.65  # Training examples: 0 positive, 0 negative
% 38.46/38.65  # Parsed axioms                        : 18
% 38.46/38.65  # Removed by relevancy pruning/SinE    : 0
% 38.46/38.65  # Initial clauses                      : 30
% 38.46/38.65  # Removed in clause preprocessing      : 1
% 38.46/38.65  # Initial clauses in saturation        : 29
% 38.46/38.65  # Processed clauses                    : 162411
% 38.46/38.65  # ...of these trivial                  : 2147
% 38.46/38.65  # ...subsumed                          : 147974
% 38.46/38.65  # ...remaining for further processing  : 12290
% 38.46/38.65  # Other redundant clauses eliminated   : 4
% 38.46/38.65  # Clauses deleted for lack of memory   : 115214
% 38.46/38.65  # Backward-subsumed                    : 1034
% 38.46/38.65  # Backward-rewritten                   : 693
% 38.46/38.65  # Generated clauses                    : 3583340
% 38.46/38.65  # ...of the previous two non-trivial   : 3111271
% 38.46/38.65  # Contextual simplify-reflections      : 167
% 38.46/38.65  # Paramodulations                      : 3582982
% 38.46/38.65  # Factorizations                       : 354
% 38.46/38.65  # Equation resolutions                 : 4
% 38.46/38.65  # Propositional unsat checks           : 2
% 38.46/38.65  #    Propositional check models        : 0
% 38.46/38.65  #    Propositional check unsatisfiable : 0
% 38.46/38.65  #    Propositional clauses             : 0
% 38.46/38.65  #    Propositional clauses after purity: 0
% 38.46/38.65  #    Propositional unsat core size     : 0
% 38.46/38.65  #    Propositional preprocessing time  : 0.000
% 38.46/38.65  #    Propositional encoding time       : 3.848
% 38.46/38.65  #    Propositional solver time         : 1.008
% 38.46/38.66  #    Success case prop preproc time    : 0.000
% 38.46/38.66  #    Success case prop encoding time   : 0.000
% 38.46/38.66  #    Success case prop solver time     : 0.000
% 38.46/38.66  # Current number of processed clauses  : 10531
% 38.46/38.66  #    Positive orientable unit clauses  : 1534
% 38.46/38.66  #    Positive unorientable unit clauses: 3
% 38.46/38.66  #    Negative unit clauses             : 504
% 38.46/38.66  #    Non-unit-clauses                  : 8490
% 38.46/38.66  # Current number of unprocessed clauses: 1870211
% 38.46/38.66  # ...number of literals in the above   : 6141828
% 38.46/38.66  # Current number of archived formulas  : 0
% 38.46/38.66  # Current number of archived clauses   : 1756
% 38.46/38.66  # Clause-clause subsumption calls (NU) : 17723283
% 38.46/38.66  # Rec. Clause-clause subsumption calls : 7911422
% 38.46/38.66  # Non-unit clause-clause subsumptions  : 71017
% 38.46/38.66  # Unit Clause-clause subsumption calls : 827311
% 38.46/38.66  # Rewrite failures with RHS unbound    : 121
% 38.46/38.66  # BW rewrite match attempts            : 90977
% 38.46/38.66  # BW rewrite match successes           : 245
% 38.46/38.66  # Condensation attempts                : 0
% 38.46/38.66  # Condensation successes               : 0
% 38.46/38.66  # Termbank termtop insertions          : 118894633
% 38.46/38.75  
% 38.46/38.75  # -------------------------------------------------
% 38.46/38.75  # User time                : 37.272 s
% 38.46/38.75  # System time              : 1.097 s
% 38.46/38.75  # Total time               : 38.369 s
% 38.46/38.75  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
