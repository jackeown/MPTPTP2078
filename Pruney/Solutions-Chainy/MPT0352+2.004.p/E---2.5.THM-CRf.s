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
% DateTime   : Thu Dec  3 10:45:37 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 379 expanded)
%              Number of clauses        :   73 ( 172 expanded)
%              Number of leaves         :   24 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :  242 ( 727 expanded)
%              Number of equality atoms :   53 ( 225 expanded)
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

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ( r1_tarski(X2,X3)
            <=> r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_subset_1])).

fof(c_0_25,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_tarski(X33,X34)
      | ~ r1_xboole_0(X33,X35)
      | r1_tarski(X33,k4_xboole_0(X34,X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).

fof(c_0_26,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_27,plain,(
    ! [X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(X53))
      | k3_subset_1(X53,X54) = k4_xboole_0(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_28,plain,(
    ! [X18,X19] : r1_tarski(k4_xboole_0(X18,X19),X18) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_29,plain,(
    ! [X51,X52] :
      ( ( ~ m1_subset_1(X52,X51)
        | r2_hidden(X52,X51)
        | v1_xboole_0(X51) )
      & ( ~ r2_hidden(X52,X51)
        | m1_subset_1(X52,X51)
        | v1_xboole_0(X51) )
      & ( ~ m1_subset_1(X52,X51)
        | v1_xboole_0(X52)
        | ~ v1_xboole_0(X51) )
      & ( ~ v1_xboole_0(X52)
        | m1_subset_1(X52,X51)
        | ~ v1_xboole_0(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_30,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ( ~ r1_tarski(esk3_0,esk4_0)
      | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) )
    & ( r1_tarski(esk3_0,esk4_0)
      | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_31,plain,(
    ! [X55] : ~ v1_xboole_0(k1_zfmisc_1(X55)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | r1_xboole_0(X30,k4_xboole_0(X32,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).

fof(c_0_37,plain,(
    ! [X42,X43,X44,X45,X46,X47] :
      ( ( ~ r2_hidden(X44,X43)
        | r1_tarski(X44,X42)
        | X43 != k1_zfmisc_1(X42) )
      & ( ~ r1_tarski(X45,X42)
        | r2_hidden(X45,X43)
        | X43 != k1_zfmisc_1(X42) )
      & ( ~ r2_hidden(esk1_2(X46,X47),X47)
        | ~ r1_tarski(esk1_2(X46,X47),X46)
        | X47 = k1_zfmisc_1(X46) )
      & ( r2_hidden(esk1_2(X46,X47),X47)
        | r1_tarski(esk1_2(X46,X47),X46)
        | X47 = k1_zfmisc_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_43,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_33])).

fof(c_0_44,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

fof(c_0_48,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_tarski(X15,X16)
      | ~ r1_tarski(X16,X17)
      | r1_tarski(X15,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_49,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k3_subset_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,plain,
    ( r1_tarski(k3_subset_1(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_33])).

fof(c_0_55,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(X28,X29),X29) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | k1_zfmisc_1(esk2_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_57,plain,(
    ! [X49,X50] : k3_tarski(k2_tarski(X49,X50)) = k2_xboole_0(X49,X50) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_58,plain,(
    ! [X40,X41] : k1_enumset1(X40,X40,X41) = k2_tarski(X40,X41) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_59,plain,(
    ! [X11,X12,X13] :
      ( ( r1_tarski(X11,X12)
        | ~ r1_tarski(X11,k4_xboole_0(X12,X13)) )
      & ( r1_xboole_0(X11,X13)
        | ~ r1_tarski(X11,k4_xboole_0(X12,X13)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_60,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    | r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_62,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_39])).

cnf(c_0_66,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_67,plain,(
    ! [X23,X24] :
      ( v1_xboole_0(X24)
      | ~ r1_tarski(X24,X23)
      | ~ r1_xboole_0(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).

cnf(c_0_68,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_56])).

fof(c_0_70,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,k2_xboole_0(X26,X27))
      | ~ r1_xboole_0(X25,X27)
      | r1_tarski(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).

cnf(c_0_71,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_73,plain,(
    ! [X20,X21] : k2_xboole_0(X20,k4_xboole_0(X21,X20)) = k2_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))
    | r1_tarski(esk3_0,esk4_0)
    | ~ r1_tarski(X1,k3_subset_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_76,plain,
    ( r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_62])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0)
    | ~ r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k3_subset_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_42])).

fof(c_0_79,plain,(
    ! [X36,X37] : k2_xboole_0(X36,X37) = k5_xboole_0(X36,k4_xboole_0(X37,X36)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_81,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_33])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_69])).

fof(c_0_83,plain,(
    ! [X22] : k4_xboole_0(k1_xboole_0,X22) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

fof(c_0_84,plain,(
    ! [X14] : k2_xboole_0(X14,k1_xboole_0) = X14 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_86,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_87,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_88,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_74,c_0_33])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),k3_subset_1(esk2_0,esk3_0))
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tarski(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_39])])).

cnf(c_0_91,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

fof(c_0_92,plain,(
    ! [X6] :
      ( ~ v1_xboole_0(X6)
      | X6 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_93,plain,
    ( v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | ~ r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_43])).

cnf(c_0_95,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_96,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_98,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_86]),c_0_86]),c_0_33])).

cnf(c_0_99,plain,
    ( r1_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_subset_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_42])).

cnf(c_0_100,negated_conjecture,
    ( r1_tarski(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),k3_subset_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_89,c_0_90])).

fof(c_0_101,plain,(
    ! [X38,X39] : k2_tarski(X38,X39) = k2_tarski(X39,X38) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_102,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_86]),c_0_33])).

cnf(c_0_103,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_62])).

cnf(c_0_105,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_95,c_0_33])).

cnf(c_0_106,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_96,c_0_86])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_51]),c_0_40])).

cnf(c_0_108,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_109,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1))) = k3_tarski(k1_enumset1(X1,X1,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_42])).

cnf(c_0_110,negated_conjecture,
    ( r1_xboole_0(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_51])])).

cnf(c_0_111,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_101])).

cnf(c_0_112,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) = k3_tarski(k1_enumset1(X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_62])).

cnf(c_0_113,negated_conjecture,
    ( k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_114,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_105]),c_0_106])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk3_0,X1)
    | k1_zfmisc_1(esk2_0) != k1_zfmisc_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_107])).

cnf(c_0_116,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))
    | ~ r1_xboole_0(X1,k5_xboole_0(k3_subset_1(X3,X2),k3_xboole_0(X2,k3_subset_1(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_62])).

cnf(c_0_117,negated_conjecture,
    ( r1_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_110])).

cnf(c_0_118,plain,
    ( k1_enumset1(X1,X1,X2) = k1_enumset1(X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_72]),c_0_72])).

cnf(c_0_119,negated_conjecture,
    ( k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_114])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(er,[status(thm)],[c_0_115])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_39]),c_0_118]),c_0_119]),c_0_120])]),c_0_90]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:07:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.68/0.93  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.68/0.93  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.68/0.93  #
% 0.68/0.93  # Preprocessing time       : 0.027 s
% 0.68/0.93  
% 0.68/0.93  # Proof found!
% 0.68/0.93  # SZS status Theorem
% 0.68/0.93  # SZS output start CNFRefutation
% 0.68/0.93  fof(t31_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 0.68/0.93  fof(t86_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X1,X3))=>r1_tarski(X1,k4_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 0.68/0.93  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.68/0.93  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.68/0.93  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.68/0.93  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.68/0.93  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.68/0.93  fof(t85_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_xboole_0(X1,k4_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 0.68/0.93  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.68/0.93  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.68/0.93  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.68/0.93  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.68/0.93  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.68/0.93  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.68/0.93  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.68/0.93  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.68/0.93  fof(t69_xboole_1, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>~((r1_tarski(X2,X1)&r1_xboole_0(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 0.68/0.93  fof(t73_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,k2_xboole_0(X2,X3))&r1_xboole_0(X1,X3))=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 0.68/0.93  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.68/0.93  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.68/0.93  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 0.68/0.93  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.68/0.93  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.68/0.93  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.68/0.93  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r1_tarski(X2,X3)<=>r1_tarski(k3_subset_1(X1,X3),k3_subset_1(X1,X2)))))), inference(assume_negation,[status(cth)],[t31_subset_1])).
% 0.68/0.93  fof(c_0_25, plain, ![X33, X34, X35]:(~r1_tarski(X33,X34)|~r1_xboole_0(X33,X35)|r1_tarski(X33,k4_xboole_0(X34,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t86_xboole_1])])).
% 0.68/0.93  fof(c_0_26, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.68/0.93  fof(c_0_27, plain, ![X53, X54]:(~m1_subset_1(X54,k1_zfmisc_1(X53))|k3_subset_1(X53,X54)=k4_xboole_0(X53,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.68/0.93  fof(c_0_28, plain, ![X18, X19]:r1_tarski(k4_xboole_0(X18,X19),X18), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.68/0.93  fof(c_0_29, plain, ![X51, X52]:(((~m1_subset_1(X52,X51)|r2_hidden(X52,X51)|v1_xboole_0(X51))&(~r2_hidden(X52,X51)|m1_subset_1(X52,X51)|v1_xboole_0(X51)))&((~m1_subset_1(X52,X51)|v1_xboole_0(X52)|~v1_xboole_0(X51))&(~v1_xboole_0(X52)|m1_subset_1(X52,X51)|~v1_xboole_0(X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.68/0.93  fof(c_0_30, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))&((~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))&(r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.68/0.93  fof(c_0_31, plain, ![X55]:~v1_xboole_0(k1_zfmisc_1(X55)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.68/0.93  cnf(c_0_32, plain, (r1_tarski(X1,k4_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.68/0.93  cnf(c_0_33, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.68/0.93  cnf(c_0_34, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.68/0.93  cnf(c_0_35, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.68/0.93  fof(c_0_36, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|r1_xboole_0(X30,k4_xboole_0(X32,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t85_xboole_1])])).
% 0.68/0.93  fof(c_0_37, plain, ![X42, X43, X44, X45, X46, X47]:(((~r2_hidden(X44,X43)|r1_tarski(X44,X42)|X43!=k1_zfmisc_1(X42))&(~r1_tarski(X45,X42)|r2_hidden(X45,X43)|X43!=k1_zfmisc_1(X42)))&((~r2_hidden(esk1_2(X46,X47),X47)|~r1_tarski(esk1_2(X46,X47),X46)|X47=k1_zfmisc_1(X46))&(r2_hidden(esk1_2(X46,X47),X47)|r1_tarski(esk1_2(X46,X47),X46)|X47=k1_zfmisc_1(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.68/0.93  cnf(c_0_38, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.68/0.93  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.68/0.93  cnf(c_0_40, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.68/0.93  cnf(c_0_41, plain, (r1_tarski(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_32, c_0_33])).
% 0.68/0.93  cnf(c_0_42, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_34, c_0_33])).
% 0.68/0.93  cnf(c_0_43, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X1)), inference(rw,[status(thm)],[c_0_35, c_0_33])).
% 0.68/0.93  fof(c_0_44, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.68/0.93  cnf(c_0_45, plain, (r1_xboole_0(X1,k4_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.68/0.93  cnf(c_0_46, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.68/0.93  cnf(c_0_47, negated_conjecture, (r2_hidden(esk4_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.68/0.93  fof(c_0_48, plain, ![X15, X16, X17]:(~r1_tarski(X15,X16)|~r1_tarski(X16,X17)|r1_tarski(X15,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.68/0.93  fof(c_0_49, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.68/0.93  cnf(c_0_50, plain, (r1_tarski(X1,k3_subset_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.68/0.93  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.68/0.93  cnf(c_0_52, plain, (r1_tarski(k3_subset_1(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.68/0.93  cnf(c_0_53, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.68/0.93  cnf(c_0_54, plain, (r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_33])).
% 0.68/0.93  fof(c_0_55, plain, ![X28, X29]:r1_xboole_0(k4_xboole_0(X28,X29),X29), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.68/0.93  cnf(c_0_56, negated_conjecture, (r1_tarski(esk4_0,X1)|k1_zfmisc_1(esk2_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.68/0.93  fof(c_0_57, plain, ![X49, X50]:k3_tarski(k2_tarski(X49,X50))=k2_xboole_0(X49,X50), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.68/0.93  fof(c_0_58, plain, ![X40, X41]:k1_enumset1(X40,X40,X41)=k2_tarski(X40,X41), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.68/0.93  fof(c_0_59, plain, ![X11, X12, X13]:((r1_tarski(X11,X12)|~r1_tarski(X11,k4_xboole_0(X12,X13)))&(r1_xboole_0(X11,X13)|~r1_tarski(X11,k4_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.68/0.93  cnf(c_0_60, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.68/0.93  cnf(c_0_61, negated_conjecture, (r1_tarski(esk3_0,esk4_0)|r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.68/0.93  cnf(c_0_62, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.68/0.93  cnf(c_0_63, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_tarski(k3_subset_1(esk2_0,esk4_0),k3_subset_1(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.68/0.93  cnf(c_0_64, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))|~r1_tarski(X1,esk2_0)|~r1_xboole_0(X1,esk3_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.68/0.93  cnf(c_0_65, negated_conjecture, (r1_tarski(k3_subset_1(esk2_0,esk4_0),esk2_0)), inference(spm,[status(thm)],[c_0_52, c_0_39])).
% 0.68/0.93  cnf(c_0_66, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.68/0.93  fof(c_0_67, plain, ![X23, X24]:(v1_xboole_0(X24)|(~r1_tarski(X24,X23)|~r1_xboole_0(X24,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_xboole_1])])])).
% 0.68/0.93  cnf(c_0_68, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.68/0.93  cnf(c_0_69, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(er,[status(thm)],[c_0_56])).
% 0.68/0.93  fof(c_0_70, plain, ![X25, X26, X27]:(~r1_tarski(X25,k2_xboole_0(X26,X27))|~r1_xboole_0(X25,X27)|r1_tarski(X25,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t73_xboole_1])])).
% 0.68/0.93  cnf(c_0_71, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.68/0.93  cnf(c_0_72, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.68/0.93  fof(c_0_73, plain, ![X20, X21]:k2_xboole_0(X20,k4_xboole_0(X21,X20))=k2_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.68/0.93  cnf(c_0_74, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.68/0.93  cnf(c_0_75, negated_conjecture, (r1_tarski(X1,k3_subset_1(esk2_0,esk3_0))|r1_tarski(esk3_0,esk4_0)|~r1_tarski(X1,k3_subset_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.68/0.93  cnf(c_0_76, plain, (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_43, c_0_62])).
% 0.68/0.93  cnf(c_0_77, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)|~r1_xboole_0(k3_subset_1(esk2_0,esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.68/0.93  cnf(c_0_78, plain, (r1_xboole_0(k3_subset_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_66, c_0_42])).
% 0.68/0.93  fof(c_0_79, plain, ![X36, X37]:k2_xboole_0(X36,X37)=k5_xboole_0(X36,k4_xboole_0(X37,X36)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.68/0.93  cnf(c_0_80, plain, (v1_xboole_0(X1)|~r1_tarski(X1,X2)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.68/0.93  cnf(c_0_81, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_68, c_0_33])).
% 0.68/0.93  cnf(c_0_82, negated_conjecture, (r1_tarski(X1,esk2_0)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_60, c_0_69])).
% 0.68/0.93  fof(c_0_83, plain, ![X22]:k4_xboole_0(k1_xboole_0,X22)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.68/0.93  fof(c_0_84, plain, ![X14]:k2_xboole_0(X14,k1_xboole_0)=X14, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.68/0.93  cnf(c_0_85, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.68/0.93  cnf(c_0_86, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_71, c_0_72])).
% 0.68/0.93  cnf(c_0_87, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.68/0.93  cnf(c_0_88, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(rw,[status(thm)],[c_0_74, c_0_33])).
% 0.68/0.93  cnf(c_0_89, negated_conjecture, (r1_tarski(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),k3_subset_1(esk2_0,esk3_0))|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.68/0.93  cnf(c_0_90, negated_conjecture, (~r1_tarski(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_39])])).
% 0.68/0.93  cnf(c_0_91, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.68/0.93  fof(c_0_92, plain, ![X6]:(~v1_xboole_0(X6)|X6=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.68/0.93  cnf(c_0_93, plain, (v1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)))|~r1_tarski(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.68/0.93  cnf(c_0_94, negated_conjecture, (r1_tarski(k5_xboole_0(esk4_0,k3_xboole_0(esk4_0,X1)),esk2_0)), inference(spm,[status(thm)],[c_0_82, c_0_43])).
% 0.68/0.93  cnf(c_0_95, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.68/0.93  cnf(c_0_96, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.68/0.93  cnf(c_0_97, plain, (r1_tarski(X1,X2)|~r1_xboole_0(X1,X3)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.68/0.93  cnf(c_0_98, plain, (k3_tarski(k1_enumset1(X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_86]), c_0_86]), c_0_33])).
% 0.68/0.93  cnf(c_0_99, plain, (r1_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_subset_1(X3,X2))), inference(spm,[status(thm)],[c_0_88, c_0_42])).
% 0.68/0.93  cnf(c_0_100, negated_conjecture, (r1_tarski(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),k3_subset_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[c_0_89, c_0_90])).
% 0.68/0.93  fof(c_0_101, plain, ![X38, X39]:k2_tarski(X38,X39)=k2_tarski(X39,X38), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.68/0.93  cnf(c_0_102, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_86]), c_0_33])).
% 0.68/0.93  cnf(c_0_103, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.68/0.93  cnf(c_0_104, negated_conjecture, (v1_xboole_0(k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_62])).
% 0.68/0.93  cnf(c_0_105, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_95, c_0_33])).
% 0.68/0.93  cnf(c_0_106, plain, (k3_tarski(k1_enumset1(X1,X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_96, c_0_86])).
% 0.68/0.93  cnf(c_0_107, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_51]), c_0_40])).
% 0.68/0.93  cnf(c_0_108, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_xboole_0(X1,k5_xboole_0(X3,k3_xboole_0(X3,X2)))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.68/0.93  cnf(c_0_109, plain, (k3_tarski(k1_enumset1(X1,X1,k3_subset_1(X2,X1)))=k3_tarski(k1_enumset1(X1,X1,X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_98, c_0_42])).
% 0.68/0.93  cnf(c_0_110, negated_conjecture, (r1_xboole_0(k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_51])])).
% 0.68/0.93  cnf(c_0_111, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_101])).
% 0.68/0.93  cnf(c_0_112, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))=k3_tarski(k1_enumset1(X1,X1,X2))), inference(spm,[status(thm)],[c_0_102, c_0_62])).
% 0.68/0.93  cnf(c_0_113, negated_conjecture, (k5_xboole_0(esk4_0,k3_xboole_0(esk2_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.68/0.93  cnf(c_0_114, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_105]), c_0_106])).
% 0.68/0.93  cnf(c_0_115, negated_conjecture, (r1_tarski(esk3_0,X1)|k1_zfmisc_1(esk2_0)!=k1_zfmisc_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_107])).
% 0.68/0.93  cnf(c_0_116, plain, (r1_tarski(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~r1_tarski(X1,k3_tarski(k1_enumset1(X2,X2,X3)))|~r1_xboole_0(X1,k5_xboole_0(k3_subset_1(X3,X2),k3_xboole_0(X2,k3_subset_1(X3,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_62])).
% 0.68/0.93  cnf(c_0_117, negated_conjecture, (r1_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk4_0),k3_xboole_0(X1,k3_subset_1(esk2_0,esk4_0))))), inference(spm,[status(thm)],[c_0_53, c_0_110])).
% 0.68/0.93  cnf(c_0_118, plain, (k1_enumset1(X1,X1,X2)=k1_enumset1(X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_72]), c_0_72])).
% 0.68/0.93  cnf(c_0_119, negated_conjecture, (k3_tarski(k1_enumset1(esk2_0,esk2_0,esk4_0))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_114])).
% 0.68/0.93  cnf(c_0_120, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(er,[status(thm)],[c_0_115])).
% 0.68/0.93  cnf(c_0_121, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_39]), c_0_118]), c_0_119]), c_0_120])]), c_0_90]), ['proof']).
% 0.68/0.93  # SZS output end CNFRefutation
% 0.68/0.93  # Proof object total steps             : 122
% 0.68/0.93  # Proof object clause steps            : 73
% 0.68/0.93  # Proof object formula steps           : 49
% 0.68/0.93  # Proof object conjectures             : 28
% 0.68/0.93  # Proof object clause conjectures      : 25
% 0.68/0.93  # Proof object formula conjectures     : 3
% 0.68/0.93  # Proof object initial clauses used    : 27
% 0.68/0.93  # Proof object initial formulas used   : 24
% 0.68/0.93  # Proof object generating inferences   : 32
% 0.68/0.93  # Proof object simplifying inferences  : 36
% 0.68/0.93  # Training examples: 0 positive, 0 negative
% 0.68/0.93  # Parsed axioms                        : 24
% 0.68/0.93  # Removed by relevancy pruning/SinE    : 0
% 0.68/0.93  # Initial clauses                      : 34
% 0.68/0.93  # Removed in clause preprocessing      : 3
% 0.68/0.93  # Initial clauses in saturation        : 31
% 0.68/0.93  # Processed clauses                    : 5729
% 0.68/0.93  # ...of these trivial                  : 233
% 0.68/0.93  # ...subsumed                          : 4154
% 0.68/0.93  # ...remaining for further processing  : 1342
% 0.68/0.93  # Other redundant clauses eliminated   : 0
% 0.68/0.93  # Clauses deleted for lack of memory   : 0
% 0.68/0.93  # Backward-subsumed                    : 145
% 0.68/0.93  # Backward-rewritten                   : 202
% 0.68/0.93  # Generated clauses                    : 37706
% 0.68/0.93  # ...of the previous two non-trivial   : 29485
% 0.68/0.93  # Contextual simplify-reflections      : 26
% 0.68/0.93  # Paramodulations                      : 37504
% 0.68/0.93  # Factorizations                       : 70
% 0.68/0.93  # Equation resolutions                 : 100
% 0.68/0.93  # Propositional unsat checks           : 0
% 0.68/0.93  #    Propositional check models        : 0
% 0.68/0.93  #    Propositional check unsatisfiable : 0
% 0.68/0.93  #    Propositional clauses             : 0
% 0.68/0.93  #    Propositional clauses after purity: 0
% 0.68/0.93  #    Propositional unsat core size     : 0
% 0.68/0.93  #    Propositional preprocessing time  : 0.000
% 0.68/0.93  #    Propositional encoding time       : 0.000
% 0.68/0.93  #    Propositional solver time         : 0.000
% 0.68/0.93  #    Success case prop preproc time    : 0.000
% 0.68/0.93  #    Success case prop encoding time   : 0.000
% 0.68/0.93  #    Success case prop solver time     : 0.000
% 0.68/0.93  # Current number of processed clauses  : 963
% 0.68/0.93  #    Positive orientable unit clauses  : 131
% 0.68/0.93  #    Positive unorientable unit clauses: 2
% 0.68/0.93  #    Negative unit clauses             : 23
% 0.68/0.93  #    Non-unit-clauses                  : 807
% 0.68/0.93  # Current number of unprocessed clauses: 23151
% 0.68/0.93  # ...number of literals in the above   : 82520
% 0.68/0.93  # Current number of archived formulas  : 0
% 0.68/0.93  # Current number of archived clauses   : 382
% 0.68/0.93  # Clause-clause subsumption calls (NU) : 137420
% 0.68/0.93  # Rec. Clause-clause subsumption calls : 111449
% 0.68/0.93  # Non-unit clause-clause subsumptions  : 2748
% 0.68/0.93  # Unit Clause-clause subsumption calls : 7773
% 0.68/0.93  # Rewrite failures with RHS unbound    : 0
% 0.68/0.93  # BW rewrite match attempts            : 865
% 0.68/0.93  # BW rewrite match successes           : 101
% 0.68/0.93  # Condensation attempts                : 0
% 0.68/0.93  # Condensation successes               : 0
% 0.68/0.93  # Termbank termtop insertions          : 660647
% 0.77/0.93  
% 0.77/0.93  # -------------------------------------------------
% 0.77/0.93  # User time                : 0.571 s
% 0.77/0.93  # System time              : 0.024 s
% 0.77/0.93  # Total time               : 0.595 s
% 0.77/0.93  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
