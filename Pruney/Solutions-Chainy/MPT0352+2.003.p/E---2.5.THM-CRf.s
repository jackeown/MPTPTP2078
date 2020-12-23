%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:36 EST 2020

% Result     : Theorem 8.68s
% Output     : CNFRefutation 8.68s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 364 expanded)
%              Number of clauses        :   74 ( 165 expanded)
%              Number of leaves         :   25 (  93 expanded)
%              Depth                    :   12
%              Number of atoms          :  248 ( 715 expanded)
%              Number of equality atoms :   53 ( 207 expanded)
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

fof(t86_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,k4_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

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

fof(t85_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_xboole_0(X1,k4_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t69_xboole_1,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_tarski(X2,X1)
          & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(t73_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,k2_xboole_0(X2,X3))
        & r1_xboole_0(X1,X3) )
     => r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_26,plain,(
    ! [X35,X36,X37] :
      ( ~ r1_tarski(X35,X36)
      | ~ r1_xboole_0(X35,X37)
      | r1_tarski(X35,k4_xboole_0(X36,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_27,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_28,plain,(
    ! [X55,X56] :
      ( ~ m1_subset_1(X56,k1_zfmisc_1(X55))
      | k3_subset_1(X55,X56) = k4_xboole_0(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_29,plain,(
    ! [X19,X20] : r1_tarski(k4_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_30,plain,(
    ! [X53,X54] :
      ( ( ~ m1_subset_1(X54,X53)
        | r2_hidden(X54,X53)
        | v1_xboole_0(X53) )
      & ( ~ r2_hidden(X54,X53)
        | m1_subset_1(X54,X53)
        | v1_xboole_0(X53) )
      & ( ~ m1_subset_1(X54,X53)
        | v1_xboole_0(X54)
        | ~ v1_xboole_0(X53) )
      & ( ~ v1_xboole_0(X54)
        | m1_subset_1(X54,X53)
        | ~ v1_xboole_0(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

fof(c_0_32,plain,(
    ! [X57] : ~ v1_xboole_0(k1_zfmisc_1(X57)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_37,plain,(
    ! [X32,X33,X34] :
      ( ~ r1_tarski(X32,X33)
      | r1_xboole_0(X32,k4_xboole_0(X34,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_38,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X46,X45)
        | r1_tarski(X46,X44)
        | X45 != k1_zfmisc_1(X44) )
      & ( ~ r1_tarski(X47,X44)
        | r2_hidden(X47,X45)
        | X45 != k1_zfmisc_1(X44) )
      & ( ~ r2_hidden(esk1_2(X48,X49),X49)
        | ~ r1_tarski(esk1_2(X48,X49),X48)
        | X49 = k1_zfmisc_1(X48) )
      & ( r2_hidden(esk1_2(X48,X49),X49)
        | r1_tarski(esk1_2(X48,X49),X48)
        | X49 = k1_zfmisc_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_44,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_36,c_0_34])).

fof(c_0_45,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_46,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

fof(c_0_49,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X17,X18)
      | r1_tarski(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_50,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_53,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_46,c_0_34])).

fof(c_0_56,plain,(
    ! [X30,X31] : r1_xboole_0(k4_xboole_0(X30,X31),X31) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | k1_zfmisc_1(esk2_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_58,plain,(
    ! [X51,X52] : k3_tarski(k2_tarski(X51,X52)) = k2_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_59,plain,(
    ! [X42,X43] : k1_enumset1(X42,X42,X43) = k2_tarski(X42,X43) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_60,plain,(
    ! [X11,X12,X13] :
      ( ( r1_tarski(X11,X12)
        | ~ r1_tarski(X11,k4_xboole_0(X12,X13)) )
      & ( r1_xboole_0(X11,X13)
        | ~ r1_tarski(X11,k4_xboole_0(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_67,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_68,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X26)
      | ~ r1_tarski(X26,X25)
      | ~ r1_xboole_0(X26,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_69,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_57])).

fof(c_0_71,plain,(
    ! [X27,X28,X29] :
      ( ~ r1_tarski(X27,k2_xboole_0(X28,X29))
      | ~ r1_xboole_0(X27,X29)
      | r1_tarski(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_72,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_74,plain,(
    ! [X21,X22] : k2_xboole_0(X21,k4_xboole_0(X22,X21)) = k2_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))
    | r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_77,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_63])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

cnf(c_0_79,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_43])).

fof(c_0_80,plain,(
    ! [X38,X39] : k2_xboole_0(X38,X39) = k5_xboole_0(X38,k4_xboole_0(X39,X38)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_81,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_82,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_34])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_70])).

fof(c_0_84,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_85,plain,(
    ! [X24] :
      ( ~ r1_tarski(X24,k1_xboole_0)
      | X24 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_86,plain,(
    ! [X14,X15] : r1_tarski(k3_xboole_0(X14,X15),X14) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_88,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_89,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_90,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_75,c_0_34])).

cnf(c_0_91,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),k3_subset_1(esk2_0,esk3_0))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_40])])).

cnf(c_0_93,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_94,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_95,plain,
    ( v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_44])).

cnf(c_0_97,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_99,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_101,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_88]),c_0_88]),c_0_34])).

cnf(c_0_102,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_43])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),k3_subset_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_91,c_0_92])).

fof(c_0_104,plain,(
    ! [X40,X41] : k2_tarski(X40,X41) = k2_tarski(X41,X40) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_105,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_88]),c_0_34])).

cnf(c_0_106,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_107,negated_conjecture,
    ( v1_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_63])).

cnf(c_0_108,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_97,c_0_34])).

cnf(c_0_109,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_52]),c_0_41])).

cnf(c_0_111,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_112,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1))) = k3_tarski(k1_enumset1(X1,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_43])).

cnf(c_0_113,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_52])])).

cnf(c_0_114,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_115,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_63])).

cnf(c_0_116,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_117,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_63]),c_0_109])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | k1_zfmisc_1(esk2_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_110])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_xboole_0(X1,k5_xboole_0(k3_subset_1(X3,X2),k3_xboole_0(X2,k3_subset_1(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_63])).

cnf(c_0_120,negated_conjecture,
    ( r1_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_113])).

cnf(c_0_121,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_73]),c_0_73])).

cnf(c_0_122,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_118])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_40]),c_0_121]),c_0_122]),c_0_123])]),c_0_92]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 8.68/8.88  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 8.68/8.88  # and selection function PSelectComplexExceptUniqMaxHorn.
% 8.68/8.88  #
% 8.68/8.88  # Preprocessing time       : 0.029 s
% 8.68/8.88  
% 8.68/8.88  # Proof found!
% 8.68/8.88  # SZS status Theorem
% 8.68/8.88  # SZS output start CNFRefutation
% 8.68/8.88  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 8.68/8.88  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 8.68/8.88  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.68/8.88  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.68/8.88  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.68/8.88  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.68/8.88  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.68/8.88  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 8.68/8.88  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.68/8.88  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 8.68/8.88  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.68/8.88  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.68/8.88  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 8.68/8.88  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.68/8.88  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.68/8.88  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 8.68/8.88  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 8.68/8.88  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 8.68/8.88  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.68/8.88  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.68/8.88  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 8.68/8.88  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.68/8.88  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.68/8.88  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.68/8.88  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.68/8.88  fof(c_0_25, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 8.68/8.88  fof(c_0_26, plain, ![X35, X36, X37]:(~r1_tarski(X35,X36)|~r1_xboole_0(X35,X37)|r1_tarski(X35,k4_xboole_0(X36,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 8.68/8.88  fof(c_0_27, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 8.68/8.88  fof(c_0_28, plain, ![X55, X56]:(~m1_subset_1(X56,k1_zfmisc_1(X55))|k3_subset_1(X55,X56)=k4_xboole_0(X55,X56)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 8.68/8.88  fof(c_0_29, plain, ![X19, X20]:r1_tarski(k4_xboole_0(X19,X20),X19), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 8.68/8.88  fof(c_0_30, plain, ![X53, X54]:(((~m1_subset_1(X54,X53)|r2_hidden(X54,X53)|v1_xboole_0(X53))&(~r2_hidden(X54,X53)|m1_subset_1(X54,X53)|v1_xboole_0(X53)))&((~m1_subset_1(X54,X53)|v1_xboole_0(X54)|~v1_xboole_0(X53))&(~v1_xboole_0(X54)|m1_subset_1(X54,X53)|~v1_xboole_0(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 8.68/8.88  fof(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 8.68/8.88  fof(c_0_32, plain, ![X57]:~v1_xboole_0(k1_zfmisc_1(X57)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 8.68/8.88  cnf(c_0_33, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 8.68/8.88  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 8.68/8.88  cnf(c_0_35, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 8.68/8.88  cnf(c_0_36, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 8.68/8.88  fof(c_0_37, plain, ![X32, X33, X34]:(~r1_tarski(X32,X33)|r1_xboole_0(X32,k4_xboole_0(X34,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 8.68/8.88  fof(c_0_38, plain, ![X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X46,X45)|r1_tarski(X46,X44)|X45!=k1_zfmisc_1(X44))&(~r1_tarski(X47,X44)|r2_hidden(X47,X45)|X45!=k1_zfmisc_1(X44)))&((~r2_hidden(esk1_2(X48,X49),X49)|~r1_tarski(esk1_2(X48,X49),X48)|X49=k1_zfmisc_1(X48))&(r2_hidden(esk1_2(X48,X49),X49)|r1_tarski(esk1_2(X48,X49),X48)|X49=k1_zfmisc_1(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 8.68/8.88  cnf(c_0_39, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 8.68/8.88  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 8.68/8.88  cnf(c_0_41, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 8.68/8.88  cnf(c_0_42, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 8.68/8.88  cnf(c_0_43, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_35, c_0_34])).
% 8.68/8.88  cnf(c_0_44, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_36, c_0_34])).
% 8.68/8.88  fof(c_0_45, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 8.68/8.88  cnf(c_0_46, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 8.68/8.88  cnf(c_0_47, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 8.68/8.88  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 8.68/8.88  fof(c_0_49, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_tarski(X17,X18)|r1_tarski(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 8.68/8.88  fof(c_0_50, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 8.68/8.88  cnf(c_0_51, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 8.68/8.88  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 8.68/8.88  cnf(c_0_53, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 8.68/8.88  cnf(c_0_54, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 8.68/8.88  cnf(c_0_55, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_46, c_0_34])).
% 8.68/8.88  fof(c_0_56, plain, ![X30, X31]:r1_xboole_0(k4_xboole_0(X30,X31),X31), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 8.68/8.88  cnf(c_0_57, negated_conjecture, (r1_tarski(esk4_0,X1)|k1_zfmisc_1(esk2_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 8.68/8.88  fof(c_0_58, plain, ![X51, X52]:k3_tarski(k2_tarski(X51,X52))=k2_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 8.68/8.88  fof(c_0_59, plain, ![X42, X43]:k1_enumset1(X42,X42,X43)=k2_tarski(X42,X43), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 8.68/8.88  fof(c_0_60, plain, ![X11, X12, X13]:((r1_tarski(X11,X12)|~r1_tarski(X11,k4_xboole_0(X12,X13)))&(r1_xboole_0(X11,X13)|~r1_tarski(X11,k4_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 8.68/8.88  cnf(c_0_61, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 8.68/8.88  cnf(c_0_62, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 8.68/8.88  cnf(c_0_63, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 8.68/8.88  cnf(c_0_64, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 8.68/8.88  cnf(c_0_65, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))|~r1_tarski(X1,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 8.68/8.88  cnf(c_0_66, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 8.68/8.88  cnf(c_0_67, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 8.68/8.88  fof(c_0_68, plain, ![X25, X26]:(v1_xboole_0(X26)|(~r1_tarski(X26,X25)|~r1_xboole_0(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 8.68/8.88  cnf(c_0_69, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 8.68/8.88  cnf(c_0_70, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(er,[status(thm)],[c_0_57])).
% 8.68/8.88  fof(c_0_71, plain, ![X27, X28, X29]:(~r1_tarski(X27,k2_xboole_0(X28,X29))|~r1_xboole_0(X27,X29)|r1_tarski(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 8.68/8.88  cnf(c_0_72, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 8.68/8.88  cnf(c_0_73, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 8.68/8.88  fof(c_0_74, plain, ![X21, X22]:k2_xboole_0(X21,k4_xboole_0(X22,X21))=k2_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 8.68/8.88  cnf(c_0_75, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 8.68/8.88  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))|r1_tarski(esk3_0,esk4_0)|~r1_tarski(X1,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 8.68/8.88  cnf(c_0_77, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_44, c_0_63])).
% 8.68/8.88  cnf(c_0_78, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 8.68/8.88  cnf(c_0_79, plain, (r1_xboole_0(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_67, c_0_43])).
% 8.68/8.88  fof(c_0_80, plain, ![X38, X39]:k2_xboole_0(X38,X39)=k5_xboole_0(X38,k4_xboole_0(X39,X38)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 8.68/8.88  cnf(c_0_81, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 8.68/8.88  cnf(c_0_82, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_69, c_0_34])).
% 8.68/8.88  cnf(c_0_83, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_70])).
% 8.68/8.88  fof(c_0_84, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 8.68/8.88  fof(c_0_85, plain, ![X24]:(~r1_tarski(X24,k1_xboole_0)|X24=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 8.68/8.88  fof(c_0_86, plain, ![X14, X15]:r1_tarski(k3_xboole_0(X14,X15),X14), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 8.68/8.88  cnf(c_0_87, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 8.68/8.88  cnf(c_0_88, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 8.68/8.88  cnf(c_0_89, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 8.68/8.88  cnf(c_0_90, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_75, c_0_34])).
% 8.68/8.88  cnf(c_0_91, negated_conjecture, (r1_tarski(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),k3_subset_1(esk2_0,esk3_0))|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 8.68/8.88  cnf(c_0_92, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_40])])).
% 8.68/8.88  cnf(c_0_93, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 8.68/8.88  fof(c_0_94, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 8.68/8.88  cnf(c_0_95, plain, (v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 8.68/8.88  cnf(c_0_96, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_44])).
% 8.68/8.88  cnf(c_0_97, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_84])).
% 8.68/8.88  cnf(c_0_98, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 8.68/8.88  cnf(c_0_99, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 8.68/8.88  cnf(c_0_100, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 8.68/8.88  cnf(c_0_101, plain, (k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_88]), c_0_88]), c_0_34])).
% 8.68/8.88  cnf(c_0_102, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_90, c_0_43])).
% 8.68/8.88  cnf(c_0_103, negated_conjecture, (r1_tarski(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),k3_subset_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[c_0_91, c_0_92])).
% 8.68/8.88  fof(c_0_104, plain, ![X40, X41]:k2_tarski(X40,X41)=k2_tarski(X41,X40), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 8.68/8.88  cnf(c_0_105, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_88]), c_0_34])).
% 8.68/8.88  cnf(c_0_106, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 8.68/8.88  cnf(c_0_107, negated_conjecture, (v1_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_63])).
% 8.68/8.88  cnf(c_0_108, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_97, c_0_34])).
% 8.68/8.88  cnf(c_0_109, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 8.68/8.88  cnf(c_0_110, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_52]), c_0_41])).
% 8.68/8.88  cnf(c_0_111, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 8.68/8.88  cnf(c_0_112, plain, (k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1)))=k3_tarski(k1_enumset1(X1,X1,X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_101, c_0_43])).
% 8.68/8.88  cnf(c_0_113, negated_conjecture, (r1_xboole_0(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_52])])).
% 8.68/8.88  cnf(c_0_114, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 8.68/8.88  cnf(c_0_115, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_105, c_0_63])).
% 8.68/8.88  cnf(c_0_116, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 8.68/8.88  cnf(c_0_117, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_63]), c_0_109])).
% 8.68/8.88  cnf(c_0_118, negated_conjecture, (r1_tarski(esk3_0,X1)|k1_zfmisc_1(esk2_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_110])).
% 8.68/8.88  cnf(c_0_119, plain, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_xboole_0(X1,k5_xboole_0(k3_subset_1(X3,X2),k3_xboole_0(X2,k3_subset_1(X3,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_63])).
% 8.68/8.88  cnf(c_0_120, negated_conjecture, (r1_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_54, c_0_113])).
% 8.68/8.88  cnf(c_0_121, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_73]), c_0_73])).
% 8.68/8.88  cnf(c_0_122, negated_conjecture, (k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_117])).
% 8.68/8.88  cnf(c_0_123, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(er,[status(thm)],[c_0_118])).
% 8.68/8.88  cnf(c_0_124, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_40]), c_0_121]), c_0_122]), c_0_123])]), c_0_92]), ['proof']).
% 8.68/8.88  # SZS output end CNFRefutation
% 8.68/8.88  # Proof object total steps             : 125
% 8.68/8.88  # Proof object clause steps            : 74
% 8.68/8.88  # Proof object formula steps           : 51
% 8.68/8.88  # Proof object conjectures             : 28
% 8.68/8.88  # Proof object clause conjectures      : 25
% 8.68/8.88  # Proof object formula conjectures     : 3
% 8.68/8.88  # Proof object initial clauses used    : 28
% 8.68/8.88  # Proof object initial formulas used   : 25
% 8.68/8.88  # Proof object generating inferences   : 33
% 8.68/8.88  # Proof object simplifying inferences  : 35
% 8.68/8.88  # Training examples: 0 positive, 0 negative
% 8.68/8.88  # Parsed axioms                        : 25
% 8.68/8.88  # Removed by relevancy pruning/SinE    : 0
% 8.68/8.88  # Initial clauses                      : 35
% 8.68/8.88  # Removed in clause preprocessing      : 3
% 8.68/8.88  # Initial clauses in saturation        : 32
% 8.68/8.88  # Processed clauses                    : 26729
% 8.68/8.88  # ...of these trivial                  : 1292
% 8.68/8.88  # ...subsumed                          : 20136
% 8.68/8.88  # ...remaining for further processing  : 5301
% 8.68/8.88  # Other redundant clauses eliminated   : 0
% 8.68/8.88  # Clauses deleted for lack of memory   : 0
% 8.68/8.88  # Backward-subsumed                    : 380
% 8.68/8.88  # Backward-rewritten                   : 381
% 8.68/8.88  # Generated clauses                    : 801058
% 8.68/8.88  # ...of the previous two non-trivial   : 640339
% 8.68/8.88  # Contextual simplify-reflections      : 86
% 8.68/8.88  # Paramodulations                      : 800684
% 8.68/8.88  # Factorizations                       : 104
% 8.68/8.88  # Equation resolutions                 : 200
% 8.68/8.88  # Propositional unsat checks           : 0
% 8.68/8.88  #    Propositional check models        : 0
% 8.68/8.88  #    Propositional check unsatisfiable : 0
% 8.68/8.88  #    Propositional clauses             : 0
% 8.68/8.88  #    Propositional clauses after purity: 0
% 8.68/8.88  #    Propositional unsat core size     : 0
% 8.68/8.88  #    Propositional preprocessing time  : 0.000
% 8.68/8.88  #    Propositional encoding time       : 0.000
% 8.68/8.88  #    Propositional solver time         : 0.000
% 8.68/8.88  #    Success case prop preproc time    : 0.000
% 8.68/8.88  #    Success case prop encoding time   : 0.000
% 8.68/8.88  #    Success case prop solver time     : 0.000
% 8.68/8.88  # Current number of processed clauses  : 4470
% 8.68/8.88  #    Positive orientable unit clauses  : 1321
% 8.68/8.88  #    Positive unorientable unit clauses: 2
% 8.68/8.88  #    Negative unit clauses             : 40
% 8.68/8.88  #    Non-unit-clauses                  : 3107
% 8.68/8.88  # Current number of unprocessed clauses: 611563
% 8.68/8.88  # ...number of literals in the above   : 1672190
% 8.68/8.88  # Current number of archived formulas  : 0
% 8.68/8.88  # Current number of archived clauses   : 834
% 8.68/8.88  # Clause-clause subsumption calls (NU) : 1278364
% 8.68/8.88  # Rec. Clause-clause subsumption calls : 1011900
% 8.68/8.88  # Non-unit clause-clause subsumptions  : 13573
% 8.68/8.88  # Unit Clause-clause subsumption calls : 35933
% 8.68/8.88  # Rewrite failures with RHS unbound    : 0
% 8.68/8.88  # BW rewrite match attempts            : 70989
% 8.68/8.88  # BW rewrite match successes           : 135
% 8.68/8.88  # Condensation attempts                : 0
% 8.68/8.88  # Condensation successes               : 0
% 8.68/8.88  # Termbank termtop insertions          : 18796050
% 8.75/8.91  
% 8.75/8.91  # -------------------------------------------------
% 8.75/8.91  # User time                : 8.247 s
% 8.75/8.91  # System time              : 0.327 s
% 8.75/8.91  # Total time               : 8.575 s
% 8.75/8.91  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
