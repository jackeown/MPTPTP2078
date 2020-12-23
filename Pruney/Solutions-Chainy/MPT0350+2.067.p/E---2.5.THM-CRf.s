%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:23 EST 2020

% Result     : Theorem 6.52s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :  119 (5304 expanded)
%              Number of clauses        :   76 (2487 expanded)
%              Number of leaves         :   21 (1398 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 (7082 expanded)
%              Number of equality atoms :  106 (5262 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t112_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

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

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(c_0_21,plain,(
    ! [X36,X37] : k3_tarski(k2_tarski(X36,X37)) = k2_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X18,X19] : k4_xboole_0(X18,k2_xboole_0(X18,X19)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_27,plain,(
    ! [X13,X14] : k2_xboole_0(X13,k3_xboole_0(X13,X14)) = X13 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

fof(c_0_28,plain,(
    ! [X25,X26] : k2_xboole_0(X25,X26) = k5_xboole_0(X25,k4_xboole_0(X26,X25)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_29,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_34,plain,(
    ! [X23,X24] : k2_xboole_0(X23,X24) = k5_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_35,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[c_0_32,c_0_30])).

fof(c_0_38,plain,(
    ! [X22] : k5_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_39,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k3_xboole_0(X15,X16) = X15 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_30]),c_0_31])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_48,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_49,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_45]),c_0_46])])).

fof(c_0_50,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_51,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(X46))
      | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
      | k4_subset_1(X46,X47,X48) = k2_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

fof(c_0_52,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_53,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).

fof(c_0_55,plain,(
    ! [X40] : k2_subset_1(X40) = X40 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_56,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_57,plain,(
    ! [X10,X11,X12] : k5_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X12,X11)) = k3_xboole_0(k5_xboole_0(X10,X12),X11) ),
    inference(variable_rename,[status(thm)],[t112_xboole_1])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_45]),c_0_46])])).

fof(c_0_60,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X31,X30)
        | r1_tarski(X31,X29)
        | X30 != k1_zfmisc_1(X29) )
      & ( ~ r1_tarski(X32,X29)
        | r2_hidden(X32,X30)
        | X30 != k1_zfmisc_1(X29) )
      & ( ~ r2_hidden(esk1_2(X33,X34),X34)
        | ~ r1_tarski(esk1_2(X33,X34),X33)
        | X34 = k1_zfmisc_1(X33) )
      & ( r2_hidden(esk1_2(X33,X34),X34)
        | r1_tarski(esk1_2(X33,X34),X33)
        | X34 = k1_zfmisc_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_61,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k1_enumset1(X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_58])).

cnf(c_0_66,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(rw,[status(thm)],[c_0_53,c_0_59])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_68,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X39,X38)
        | r2_hidden(X39,X38)
        | v1_xboole_0(X38) )
      & ( ~ r2_hidden(X39,X38)
        | m1_subset_1(X39,X38)
        | v1_xboole_0(X38) )
      & ( ~ m1_subset_1(X39,X38)
        | v1_xboole_0(X39)
        | ~ v1_xboole_0(X38) )
      & ( ~ v1_xboole_0(X39)
        | m1_subset_1(X39,X38)
        | ~ v1_xboole_0(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_69,plain,(
    ! [X45] : ~ v1_xboole_0(k1_zfmisc_1(X45)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_70,plain,(
    ! [X41,X42] :
      ( ~ m1_subset_1(X42,k1_zfmisc_1(X41))
      | k3_subset_1(X41,X42) = k4_xboole_0(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_71,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_72,plain,
    ( k4_subset_1(X1,X2,X3) = k4_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_74,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X3,X2),X1)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_66]),c_0_58])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_80,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_81,negated_conjecture,
    ( k4_subset_1(X1,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_82,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X1,X2)) = k3_xboole_0(k5_xboole_0(X3,X2),X1)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_84,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_79,c_0_31])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)))) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_63]),c_0_42]),c_0_58])).

cnf(c_0_87,plain,
    ( k3_xboole_0(k5_xboole_0(X1,X2),X3) = X3
    | ~ r1_tarski(X3,k5_xboole_0(X3,X2))
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_73])).

cnf(c_0_89,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_58])).

cnf(c_0_90,plain,
    ( k3_subset_1(X1,X2) = k5_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_65]),c_0_83])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_31]),c_0_31])).

cnf(c_0_92,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_58])).

fof(c_0_93,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | m1_subset_1(k3_subset_1(X43,X44),k1_zfmisc_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_94,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)))) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_73])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1)) = esk3_0
    | ~ r1_tarski(esk3_0,k5_xboole_0(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_58])).

cnf(c_0_96,plain,
    ( k3_subset_1(X1,X2) = k3_xboole_0(X1,k5_xboole_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_89,c_0_75])).

cnf(c_0_97,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k5_xboole_0(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_90])).

cnf(c_0_98,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_91]),c_0_37])).

cnf(c_0_99,plain,
    ( k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) = k3_xboole_0(k5_xboole_0(X2,X3),X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_58])).

cnf(c_0_100,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( k5_xboole_0(esk3_0,k3_xboole_0(k3_subset_1(esk2_0,esk3_0),k5_xboole_0(k3_subset_1(esk2_0,esk3_0),esk3_0))) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_75])).

cnf(c_0_102,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k5_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_64,c_0_45])).

cnf(c_0_103,plain,
    ( k5_xboole_0(k3_subset_1(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))) = X1
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_84]),c_0_37])).

cnf(c_0_104,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_44]),c_0_58]),c_0_44]),c_0_46])])).

cnf(c_0_105,plain,
    ( k3_subset_1(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2))
    | ~ m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_106,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99]),c_0_58])).

cnf(c_0_107,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k5_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_66]),c_0_58])).

cnf(c_0_108,plain,
    ( m1_subset_1(k5_xboole_0(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_90])).

cnf(c_0_109,negated_conjecture,
    ( k3_xboole_0(k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)),k5_xboole_0(k3_subset_1(esk2_0,esk3_0),esk3_0)) != esk2_0
    | ~ m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))
    | ~ r1_tarski(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk3_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( k5_xboole_0(k3_subset_1(esk2_0,esk3_0),esk3_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_104]),c_0_73])])).

cnf(c_0_111,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_104]),c_0_73])])).

cnf(c_0_112,plain,
    ( k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2))))) = X1 ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_104])).

cnf(c_0_114,plain,
    ( m1_subset_1(k3_xboole_0(X1,k5_xboole_0(X1,X2)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(k3_xboole_0(X2,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_108,c_0_75])).

cnf(c_0_115,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)))) != esk2_0
    | ~ m1_subset_1(k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110]),c_0_58]),c_0_110]),c_0_88])]),c_0_111]),c_0_111])).

cnf(c_0_116,negated_conjecture,
    ( k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_113])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_113]),c_0_58]),c_0_104]),c_0_73])])).

cnf(c_0_118,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_113]),c_0_113]),c_0_116]),c_0_117])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 6.52/6.74  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05BN
% 6.52/6.74  # and selection function SelectUnlessUniqMaxSmallestOrientable.
% 6.52/6.74  #
% 6.52/6.74  # Preprocessing time       : 0.028 s
% 6.52/6.74  # Presaturation interreduction done
% 6.52/6.74  
% 6.52/6.74  # Proof found!
% 6.52/6.74  # SZS status Theorem
% 6.52/6.74  # SZS output start CNFRefutation
% 6.52/6.74  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.52/6.74  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.52/6.74  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.52/6.74  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.52/6.74  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 6.52/6.74  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.52/6.74  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.52/6.74  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.52/6.74  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.52/6.74  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.52/6.74  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 6.52/6.74  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.52/6.74  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.52/6.74  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.52/6.74  fof(t112_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 6.52/6.74  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.52/6.74  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.52/6.74  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.52/6.74  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.52/6.74  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.52/6.74  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.52/6.74  fof(c_0_21, plain, ![X36, X37]:k3_tarski(k2_tarski(X36,X37))=k2_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 6.52/6.74  fof(c_0_22, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.52/6.74  fof(c_0_23, plain, ![X18, X19]:k4_xboole_0(X18,k2_xboole_0(X18,X19))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 6.52/6.74  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.52/6.74  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.52/6.74  fof(c_0_26, plain, ![X8, X9]:k4_xboole_0(X8,X9)=k5_xboole_0(X8,k3_xboole_0(X8,X9)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 6.52/6.74  fof(c_0_27, plain, ![X13, X14]:k2_xboole_0(X13,k3_xboole_0(X13,X14))=X13, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 6.52/6.74  fof(c_0_28, plain, ![X25, X26]:k2_xboole_0(X25,X26)=k5_xboole_0(X25,k4_xboole_0(X26,X25)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 6.52/6.74  cnf(c_0_29, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.52/6.74  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 6.52/6.74  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.52/6.74  cnf(c_0_32, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.52/6.74  fof(c_0_33, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 6.52/6.74  fof(c_0_34, plain, ![X23, X24]:k2_xboole_0(X23,X24)=k5_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 6.52/6.74  cnf(c_0_35, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.52/6.74  cnf(c_0_36, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k3_tarski(k1_enumset1(X1,X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 6.52/6.74  cnf(c_0_37, plain, (k3_tarski(k1_enumset1(X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[c_0_32, c_0_30])).
% 6.52/6.74  fof(c_0_38, plain, ![X22]:k5_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t5_boole])).
% 6.52/6.74  fof(c_0_39, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k3_xboole_0(X15,X16)=X15), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 6.52/6.74  cnf(c_0_40, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 6.52/6.74  cnf(c_0_41, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 6.52/6.74  cnf(c_0_42, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_30]), c_0_31])).
% 6.52/6.74  cnf(c_0_43, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 6.52/6.74  cnf(c_0_44, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.52/6.74  cnf(c_0_45, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 6.52/6.74  cnf(c_0_46, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_40])).
% 6.52/6.74  cnf(c_0_47, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_41, c_0_30])).
% 6.52/6.74  cnf(c_0_48, plain, (k3_tarski(k1_enumset1(X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 6.52/6.74  cnf(c_0_49, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_45]), c_0_46])])).
% 6.52/6.74  fof(c_0_50, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 6.52/6.74  fof(c_0_51, plain, ![X46, X47, X48]:(~m1_subset_1(X47,k1_zfmisc_1(X46))|~m1_subset_1(X48,k1_zfmisc_1(X46))|k4_subset_1(X46,X47,X48)=k2_xboole_0(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 6.52/6.74  fof(c_0_52, plain, ![X4, X5]:k3_xboole_0(X4,X5)=k3_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 6.52/6.74  cnf(c_0_53, plain, (k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 6.52/6.74  fof(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_50])])])).
% 6.52/6.74  fof(c_0_55, plain, ![X40]:k2_subset_1(X40)=X40, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 6.52/6.74  cnf(c_0_56, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 6.52/6.74  fof(c_0_57, plain, ![X10, X11, X12]:k5_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X12,X11))=k3_xboole_0(k5_xboole_0(X10,X12),X11), inference(variable_rename,[status(thm)],[t112_xboole_1])).
% 6.52/6.74  cnf(c_0_58, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 6.52/6.74  cnf(c_0_59, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_45]), c_0_46])])).
% 6.52/6.74  fof(c_0_60, plain, ![X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X31,X30)|r1_tarski(X31,X29)|X30!=k1_zfmisc_1(X29))&(~r1_tarski(X32,X29)|r2_hidden(X32,X30)|X30!=k1_zfmisc_1(X29)))&((~r2_hidden(esk1_2(X33,X34),X34)|~r1_tarski(esk1_2(X33,X34),X33)|X34=k1_zfmisc_1(X33))&(r2_hidden(esk1_2(X33,X34),X34)|r1_tarski(esk1_2(X33,X34),X33)|X34=k1_zfmisc_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 6.52/6.74  cnf(c_0_61, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.52/6.74  cnf(c_0_62, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_55])).
% 6.52/6.74  cnf(c_0_63, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k1_enumset1(X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_56, c_0_30])).
% 6.52/6.74  cnf(c_0_64, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X3,X2))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 6.52/6.74  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=X2|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_58])).
% 6.52/6.74  cnf(c_0_66, plain, (k3_xboole_0(X1,X1)=X1), inference(rw,[status(thm)],[c_0_53, c_0_59])).
% 6.52/6.74  cnf(c_0_67, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 6.52/6.74  fof(c_0_68, plain, ![X38, X39]:(((~m1_subset_1(X39,X38)|r2_hidden(X39,X38)|v1_xboole_0(X38))&(~r2_hidden(X39,X38)|m1_subset_1(X39,X38)|v1_xboole_0(X38)))&((~m1_subset_1(X39,X38)|v1_xboole_0(X39)|~v1_xboole_0(X38))&(~v1_xboole_0(X39)|m1_subset_1(X39,X38)|~v1_xboole_0(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 6.52/6.74  fof(c_0_69, plain, ![X45]:~v1_xboole_0(k1_zfmisc_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 6.52/6.74  fof(c_0_70, plain, ![X41, X42]:(~m1_subset_1(X42,k1_zfmisc_1(X41))|k3_subset_1(X41,X42)=k4_xboole_0(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 6.52/6.74  cnf(c_0_71, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 6.52/6.74  cnf(c_0_72, plain, (k4_subset_1(X1,X2,X3)=k4_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_63, c_0_63])).
% 6.52/6.74  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.52/6.74  cnf(c_0_74, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(k5_xboole_0(X3,X2),X1)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 6.52/6.74  cnf(c_0_75, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X1))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_66]), c_0_58])).
% 6.52/6.74  cnf(c_0_76, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_67])).
% 6.52/6.74  cnf(c_0_77, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 6.52/6.74  cnf(c_0_78, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 6.52/6.74  cnf(c_0_79, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 6.52/6.74  fof(c_0_80, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 6.52/6.74  cnf(c_0_81, negated_conjecture, (k4_subset_1(X1,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 6.52/6.74  cnf(c_0_82, plain, (k3_xboole_0(X1,k5_xboole_0(X1,X2))=k3_xboole_0(k5_xboole_0(X3,X2),X1)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 6.52/6.74  cnf(c_0_83, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 6.52/6.74  cnf(c_0_84, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_79, c_0_31])).
% 6.52/6.74  cnf(c_0_85, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 6.52/6.74  cnf(c_0_86, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))))!=esk2_0|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_63]), c_0_42]), c_0_58])).
% 6.52/6.74  cnf(c_0_87, plain, (k3_xboole_0(k5_xboole_0(X1,X2),X3)=X3|~r1_tarski(X3,k5_xboole_0(X3,X2))|~r1_tarski(X3,X1)), inference(spm,[status(thm)],[c_0_45, c_0_82])).
% 6.52/6.74  cnf(c_0_88, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_83, c_0_73])).
% 6.52/6.74  cnf(c_0_89, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X2,X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_84, c_0_58])).
% 6.52/6.74  cnf(c_0_90, plain, (k3_subset_1(X1,X2)=k5_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_65]), c_0_83])).
% 6.52/6.74  cnf(c_0_91, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_31]), c_0_31])).
% 6.52/6.74  cnf(c_0_92, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_64, c_0_58])).
% 6.52/6.74  fof(c_0_93, plain, ![X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(X43))|m1_subset_1(k3_subset_1(X43,X44),k1_zfmisc_1(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 6.52/6.74  cnf(c_0_94, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk3_0),k3_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0))))!=esk2_0|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_86, c_0_73])).
% 6.52/6.74  cnf(c_0_95, negated_conjecture, (k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,X1))=esk3_0|~r1_tarski(esk3_0,k5_xboole_0(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_58])).
% 6.52/6.74  cnf(c_0_96, plain, (k3_subset_1(X1,X2)=k3_xboole_0(X1,k5_xboole_0(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_89, c_0_75])).
% 6.52/6.74  cnf(c_0_97, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k5_xboole_0(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_84, c_0_90])).
% 6.52/6.74  cnf(c_0_98, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_91]), c_0_37])).
% 6.52/6.74  cnf(c_0_99, plain, (k5_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))=k3_xboole_0(k5_xboole_0(X2,X3),X1)), inference(spm,[status(thm)],[c_0_92, c_0_58])).
% 6.52/6.74  cnf(c_0_100, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_93])).
% 6.52/6.74  cnf(c_0_101, negated_conjecture, (k5_xboole_0(esk3_0,k3_xboole_0(k3_subset_1(esk2_0,esk3_0),k5_xboole_0(k3_subset_1(esk2_0,esk3_0),esk3_0)))!=esk2_0|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_94, c_0_75])).
% 6.52/6.74  cnf(c_0_102, plain, (k5_xboole_0(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k5_xboole_0(X1,X2),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_64, c_0_45])).
% 6.52/6.74  cnf(c_0_103, plain, (k5_xboole_0(k3_subset_1(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2)))=X1|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_84]), c_0_37])).
% 6.52/6.74  cnf(c_0_104, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_44]), c_0_58]), c_0_44]), c_0_46])])).
% 6.52/6.74  cnf(c_0_105, plain, (k3_subset_1(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))|~m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 6.52/6.74  cnf(c_0_106, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99]), c_0_58])).
% 6.52/6.74  cnf(c_0_107, plain, (k5_xboole_0(X1,k3_xboole_0(X1,X2))=k3_xboole_0(X1,k5_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_66]), c_0_58])).
% 6.52/6.74  cnf(c_0_108, plain, (m1_subset_1(k5_xboole_0(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_100, c_0_90])).
% 6.52/6.74  cnf(c_0_109, negated_conjecture, (k3_xboole_0(k5_xboole_0(esk3_0,k3_subset_1(esk2_0,esk3_0)),k5_xboole_0(k3_subset_1(esk2_0,esk3_0),esk3_0))!=esk2_0|~m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))|~r1_tarski(esk3_0,k5_xboole_0(k3_subset_1(esk2_0,esk3_0),esk3_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 6.52/6.74  cnf(c_0_110, negated_conjecture, (k5_xboole_0(k3_subset_1(esk2_0,esk3_0),esk3_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_104]), c_0_73])])).
% 6.52/6.74  cnf(c_0_111, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_104]), c_0_73])])).
% 6.52/6.74  cnf(c_0_112, plain, (k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,X2)))))=X1), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 6.52/6.74  cnf(c_0_113, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_107, c_0_104])).
% 6.52/6.74  cnf(c_0_114, plain, (m1_subset_1(k3_xboole_0(X1,k5_xboole_0(X1,X2)),k1_zfmisc_1(X1))|~m1_subset_1(k3_xboole_0(X2,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_108, c_0_75])).
% 6.52/6.74  cnf(c_0_115, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0))))!=esk2_0|~m1_subset_1(k3_xboole_0(esk2_0,k5_xboole_0(esk2_0,esk3_0)),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110]), c_0_58]), c_0_110]), c_0_88])]), c_0_111]), c_0_111])).
% 6.52/6.74  cnf(c_0_116, negated_conjecture, (k3_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_113]), c_0_113])).
% 6.52/6.74  cnf(c_0_117, negated_conjecture, (m1_subset_1(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_113]), c_0_58]), c_0_104]), c_0_73])])).
% 6.52/6.74  cnf(c_0_118, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_113]), c_0_113]), c_0_116]), c_0_117])]), ['proof']).
% 6.52/6.74  # SZS output end CNFRefutation
% 6.52/6.74  # Proof object total steps             : 119
% 6.52/6.74  # Proof object clause steps            : 76
% 6.52/6.74  # Proof object formula steps           : 43
% 6.52/6.74  # Proof object conjectures             : 21
% 6.52/6.74  # Proof object clause conjectures      : 18
% 6.52/6.74  # Proof object formula conjectures     : 3
% 6.52/6.74  # Proof object initial clauses used    : 22
% 6.52/6.74  # Proof object initial formulas used   : 21
% 6.52/6.74  # Proof object generating inferences   : 35
% 6.52/6.74  # Proof object simplifying inferences  : 64
% 6.52/6.74  # Training examples: 0 positive, 0 negative
% 6.52/6.74  # Parsed axioms                        : 22
% 6.52/6.74  # Removed by relevancy pruning/SinE    : 0
% 6.52/6.74  # Initial clauses                      : 31
% 6.52/6.74  # Removed in clause preprocessing      : 4
% 6.52/6.74  # Initial clauses in saturation        : 27
% 6.52/6.74  # Processed clauses                    : 19003
% 6.52/6.74  # ...of these trivial                  : 91
% 6.52/6.74  # ...subsumed                          : 16824
% 6.52/6.74  # ...remaining for further processing  : 2087
% 6.52/6.74  # Other redundant clauses eliminated   : 4
% 6.52/6.74  # Clauses deleted for lack of memory   : 0
% 6.52/6.74  # Backward-subsumed                    : 262
% 6.52/6.74  # Backward-rewritten                   : 350
% 6.52/6.74  # Generated clauses                    : 666113
% 6.52/6.74  # ...of the previous two non-trivial   : 635018
% 6.52/6.74  # Contextual simplify-reflections      : 68
% 6.52/6.74  # Paramodulations                      : 666107
% 6.52/6.74  # Factorizations                       : 2
% 6.52/6.74  # Equation resolutions                 : 4
% 6.52/6.74  # Propositional unsat checks           : 0
% 6.52/6.74  #    Propositional check models        : 0
% 6.52/6.74  #    Propositional check unsatisfiable : 0
% 6.52/6.74  #    Propositional clauses             : 0
% 6.52/6.74  #    Propositional clauses after purity: 0
% 6.52/6.74  #    Propositional unsat core size     : 0
% 6.52/6.74  #    Propositional preprocessing time  : 0.000
% 6.52/6.74  #    Propositional encoding time       : 0.000
% 6.52/6.74  #    Propositional solver time         : 0.000
% 6.52/6.74  #    Success case prop preproc time    : 0.000
% 6.52/6.74  #    Success case prop encoding time   : 0.000
% 6.52/6.74  #    Success case prop solver time     : 0.000
% 6.52/6.74  # Current number of processed clauses  : 1445
% 6.52/6.74  #    Positive orientable unit clauses  : 89
% 6.52/6.74  #    Positive unorientable unit clauses: 22
% 6.52/6.74  #    Negative unit clauses             : 22
% 6.52/6.74  #    Non-unit-clauses                  : 1312
% 6.52/6.74  # Current number of unprocessed clauses: 612252
% 6.52/6.74  # ...number of literals in the above   : 2146704
% 6.52/6.74  # Current number of archived formulas  : 0
% 6.52/6.74  # Current number of archived clauses   : 642
% 6.52/6.74  # Clause-clause subsumption calls (NU) : 553744
% 6.52/6.74  # Rec. Clause-clause subsumption calls : 258824
% 6.52/6.74  # Non-unit clause-clause subsumptions  : 8318
% 6.52/6.74  # Unit Clause-clause subsumption calls : 8314
% 6.52/6.74  # Rewrite failures with RHS unbound    : 0
% 6.52/6.74  # BW rewrite match attempts            : 985
% 6.52/6.74  # BW rewrite match successes           : 142
% 6.52/6.74  # Condensation attempts                : 0
% 6.52/6.74  # Condensation successes               : 0
% 6.52/6.74  # Termbank termtop insertions          : 15905070
% 6.52/6.76  
% 6.52/6.76  # -------------------------------------------------
% 6.52/6.76  # User time                : 6.160 s
% 6.52/6.76  # System time              : 0.255 s
% 6.52/6.76  # Total time               : 6.414 s
% 6.52/6.76  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
