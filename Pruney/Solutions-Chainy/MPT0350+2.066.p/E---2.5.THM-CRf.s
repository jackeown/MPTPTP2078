%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:45:23 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 680 expanded)
%              Number of clauses        :   73 ( 303 expanded)
%              Number of leaves         :   26 ( 181 expanded)
%              Depth                    :   14
%              Number of atoms          :  241 (1363 expanded)
%              Number of equality atoms :  110 ( 610 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t98_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_26,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X22,X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X23,X19)
        | r2_hidden(X23,X20)
        | r2_hidden(X23,X21)
        | X21 != k4_xboole_0(X19,X20) )
      & ( ~ r2_hidden(esk2_3(X24,X25,X26),X26)
        | ~ r2_hidden(esk2_3(X24,X25,X26),X24)
        | r2_hidden(esk2_3(X24,X25,X26),X25)
        | X26 = k4_xboole_0(X24,X25) )
      & ( r2_hidden(esk2_3(X24,X25,X26),X24)
        | r2_hidden(esk2_3(X24,X25,X26),X26)
        | X26 = k4_xboole_0(X24,X25) )
      & ( ~ r2_hidden(esk2_3(X24,X25,X26),X25)
        | r2_hidden(esk2_3(X24,X25,X26),X26)
        | X26 = k4_xboole_0(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_27,plain,(
    ! [X33,X34] : k4_xboole_0(X33,X34) = k5_xboole_0(X33,k3_xboole_0(X33,X34)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_28,plain,(
    ! [X73,X74,X75,X76,X77,X78] :
      ( ( ~ r2_hidden(X75,X74)
        | r1_tarski(X75,X73)
        | X74 != k1_zfmisc_1(X73) )
      & ( ~ r1_tarski(X76,X73)
        | r2_hidden(X76,X74)
        | X74 != k1_zfmisc_1(X73) )
      & ( ~ r2_hidden(esk4_2(X77,X78),X78)
        | ~ r1_tarski(esk4_2(X77,X78),X77)
        | X78 = k1_zfmisc_1(X77) )
      & ( r2_hidden(esk4_2(X77,X78),X78)
        | r1_tarski(esk4_2(X77,X78),X77)
        | X78 = k1_zfmisc_1(X77) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_29,plain,(
    ! [X31,X32] :
      ( ( r1_tarski(X31,X32)
        | X31 != X32 )
      & ( r1_tarski(X32,X31)
        | X31 != X32 )
      & ( ~ r1_tarski(X31,X32)
        | ~ r1_tarski(X32,X31)
        | X31 = X32 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( X3 != k5_xboole_0(X4,k3_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X35,X36] :
      ( ~ r1_tarski(X35,X36)
      | k3_xboole_0(X35,X36) = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_38,plain,(
    ! [X37] : r1_tarski(k1_xboole_0,X37) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_41,plain,(
    ! [X38,X39] : k4_xboole_0(X38,k4_xboole_0(X38,X39)) = k3_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_46,plain,(
    ! [X43] : k5_xboole_0(X43,k1_xboole_0) = X43 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_47,plain,(
    ! [X82,X83] :
      ( ( ~ m1_subset_1(X83,X82)
        | r2_hidden(X83,X82)
        | v1_xboole_0(X82) )
      & ( ~ r2_hidden(X83,X82)
        | m1_subset_1(X83,X82)
        | v1_xboole_0(X82) )
      & ( ~ m1_subset_1(X83,X82)
        | v1_xboole_0(X83)
        | ~ v1_xboole_0(X82) )
      & ( ~ v1_xboole_0(X83)
        | m1_subset_1(X83,X82)
        | ~ v1_xboole_0(X82) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_48,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))
    & k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

fof(c_0_49,plain,(
    ! [X89] : ~ v1_xboole_0(k1_zfmisc_1(X89)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | X3 != k5_xboole_0(X2,k3_xboole_0(X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_zfmisc_1(X1)))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_55,plain,(
    ! [X28,X29] :
      ( ( ~ r2_hidden(esk3_2(X28,X29),X28)
        | ~ r2_hidden(esk3_2(X28,X29),X29)
        | X28 = X29 )
      & ( r2_hidden(esk3_2(X28,X29),X28)
        | r2_hidden(esk3_2(X28,X29),X29)
        | X28 = X29 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_31]),c_0_31])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_63,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk3_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk6_0,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

fof(c_0_66,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_69,plain,(
    ! [X80,X81] : k3_tarski(k2_tarski(X80,X81)) = k2_xboole_0(X80,X81) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_70,plain,(
    ! [X46,X47] : k1_enumset1(X46,X46,X47) = k2_tarski(X46,X47) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

fof(c_0_73,plain,(
    ! [X85,X86] :
      ( ~ m1_subset_1(X86,k1_zfmisc_1(X85))
      | k3_subset_1(X85,X86) = k4_xboole_0(X85,X86) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

fof(c_0_75,plain,(
    ! [X40,X41,X42] : k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k2_xboole_0(k4_xboole_0(X40,X41),k3_xboole_0(X40,X42)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_76,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_78,plain,(
    ! [X48,X49,X50] : k2_enumset1(X48,X48,X49,X50) = k1_enumset1(X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_79,plain,(
    ! [X51,X52,X53,X54] : k3_enumset1(X51,X51,X52,X53,X54) = k2_enumset1(X51,X52,X53,X54) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_80,plain,(
    ! [X55,X56,X57,X58,X59] : k4_enumset1(X55,X55,X56,X57,X58,X59) = k3_enumset1(X55,X56,X57,X58,X59) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_81,plain,(
    ! [X60,X61,X62,X63,X64,X65] : k5_enumset1(X60,X60,X61,X62,X63,X64,X65) = k4_enumset1(X60,X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_82,plain,(
    ! [X66,X67,X68,X69,X70,X71,X72] : k6_enumset1(X66,X66,X67,X68,X69,X70,X71,X72) = k5_enumset1(X66,X67,X68,X69,X70,X71,X72) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_83,plain,(
    ! [X44,X45] : k2_xboole_0(X44,X45) = k5_xboole_0(X44,k4_xboole_0(X45,X44)) ),
    inference(variable_rename,[status(thm)],[t98_xboole_1])).

cnf(c_0_84,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) = esk6_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_71]),c_0_72])).

fof(c_0_85,plain,(
    ! [X87,X88] :
      ( ~ m1_subset_1(X88,k1_zfmisc_1(X87))
      | m1_subset_1(k3_subset_1(X87,X88),k1_zfmisc_1(X87)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_86,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(X1,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_74])).

cnf(c_0_88,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_89,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_90,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_91,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_92,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_93,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_94,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_95,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_96,negated_conjecture,
    ( k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0))) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_84])).

fof(c_0_97,plain,(
    ! [X90,X91,X92] :
      ( ~ m1_subset_1(X91,k1_zfmisc_1(X90))
      | ~ m1_subset_1(X92,k1_zfmisc_1(X90))
      | k4_subset_1(X90,X91,X92) = k2_xboole_0(X91,X92) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_98,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_99,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_86,c_0_31])).

cnf(c_0_100,negated_conjecture,
    ( k3_xboole_0(esk6_0,X1) = k1_xboole_0
    | ~ r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(esk6_0,X1)),k5_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_84])).

cnf(c_0_101,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = k3_tarski(k6_enumset1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_31]),c_0_31]),c_0_31]),c_0_31]),c_0_90]),c_0_91]),c_0_92]),c_0_93]),c_0_94])).

cnf(c_0_102,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_44,c_0_36])).

cnf(c_0_103,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_89]),c_0_31]),c_0_90]),c_0_91]),c_0_92]),c_0_93]),c_0_94])).

cnf(c_0_104,negated_conjecture,
    ( k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0)) = k5_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_96]),c_0_84])).

cnf(c_0_105,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_72])).

fof(c_0_106,plain,(
    ! [X84] : k2_subset_1(X84) = X84 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_107,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_58])).

cnf(c_0_109,negated_conjecture,
    ( k3_subset_1(esk5_0,esk6_0) = k5_xboole_0(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_58]),c_0_84])).

cnf(c_0_110,negated_conjecture,
    ( k3_xboole_0(X1,esk6_0) = k1_xboole_0
    | ~ r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(X1,esk6_0)),k5_xboole_0(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_72])).

cnf(c_0_111,plain,
    ( k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_61])).

cnf(c_0_112,negated_conjecture,
    ( k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0)) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_96,c_0_104])).

cnf(c_0_113,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_105]),c_0_54]),c_0_102])).

cnf(c_0_114,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != k2_subset_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_115,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_116,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_89]),c_0_90]),c_0_91]),c_0_92]),c_0_93]),c_0_94])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_118,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_72])).

cnf(c_0_119,negated_conjecture,
    ( k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_74]),c_0_72])).

cnf(c_0_120,negated_conjecture,
    ( k5_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_104]),c_0_112]),c_0_72]),c_0_104]),c_0_113]),c_0_105]),c_0_54])).

cnf(c_0_121,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_122,negated_conjecture,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(esk5_0,esk6_0))) = k4_subset_1(esk5_0,X1,k5_xboole_0(esk5_0,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_116,c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k5_xboole_0(esk5_0,esk6_0))) = esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_54]),c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_121,c_0_109])).

cnf(c_0_125,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_58]),c_0_123]),c_0_124]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:45:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.53  # and selection function GSelectMinInfpos.
% 0.20/0.53  #
% 0.20/0.53  # Preprocessing time       : 0.029 s
% 0.20/0.53  # Presaturation interreduction done
% 0.20/0.53  
% 0.20/0.53  # Proof found!
% 0.20/0.53  # SZS status Theorem
% 0.20/0.53  # SZS output start CNFRefutation
% 0.20/0.53  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.53  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.20/0.53  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.53  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.20/0.53  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.53  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 0.20/0.53  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.53  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 0.20/0.53  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.20/0.53  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.20/0.53  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.20/0.53  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.53  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.20/0.53  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.53  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 0.20/0.53  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.20/0.53  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.53  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.53  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.53  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.53  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.53  fof(t98_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 0.20/0.53  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.20/0.53  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.20/0.53  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.53  fof(c_0_26, plain, ![X19, X20, X21, X22, X23, X24, X25, X26]:((((r2_hidden(X22,X19)|~r2_hidden(X22,X21)|X21!=k4_xboole_0(X19,X20))&(~r2_hidden(X22,X20)|~r2_hidden(X22,X21)|X21!=k4_xboole_0(X19,X20)))&(~r2_hidden(X23,X19)|r2_hidden(X23,X20)|r2_hidden(X23,X21)|X21!=k4_xboole_0(X19,X20)))&((~r2_hidden(esk2_3(X24,X25,X26),X26)|(~r2_hidden(esk2_3(X24,X25,X26),X24)|r2_hidden(esk2_3(X24,X25,X26),X25))|X26=k4_xboole_0(X24,X25))&((r2_hidden(esk2_3(X24,X25,X26),X24)|r2_hidden(esk2_3(X24,X25,X26),X26)|X26=k4_xboole_0(X24,X25))&(~r2_hidden(esk2_3(X24,X25,X26),X25)|r2_hidden(esk2_3(X24,X25,X26),X26)|X26=k4_xboole_0(X24,X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.53  fof(c_0_27, plain, ![X33, X34]:k4_xboole_0(X33,X34)=k5_xboole_0(X33,k3_xboole_0(X33,X34)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.20/0.53  fof(c_0_28, plain, ![X73, X74, X75, X76, X77, X78]:(((~r2_hidden(X75,X74)|r1_tarski(X75,X73)|X74!=k1_zfmisc_1(X73))&(~r1_tarski(X76,X73)|r2_hidden(X76,X74)|X74!=k1_zfmisc_1(X73)))&((~r2_hidden(esk4_2(X77,X78),X78)|~r1_tarski(esk4_2(X77,X78),X77)|X78=k1_zfmisc_1(X77))&(r2_hidden(esk4_2(X77,X78),X78)|r1_tarski(esk4_2(X77,X78),X77)|X78=k1_zfmisc_1(X77)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.53  fof(c_0_29, plain, ![X31, X32]:(((r1_tarski(X31,X32)|X31!=X32)&(r1_tarski(X32,X31)|X31!=X32))&(~r1_tarski(X31,X32)|~r1_tarski(X32,X31)|X31=X32)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.53  cnf(c_0_30, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.53  cnf(c_0_31, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.53  cnf(c_0_32, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.53  cnf(c_0_33, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.53  cnf(c_0_34, plain, (X3!=k5_xboole_0(X4,k3_xboole_0(X4,X2))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.53  cnf(c_0_35, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_32])).
% 0.20/0.53  cnf(c_0_36, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.53  fof(c_0_37, plain, ![X35, X36]:(~r1_tarski(X35,X36)|k3_xboole_0(X35,X36)=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.20/0.53  fof(c_0_38, plain, ![X37]:r1_tarski(k1_xboole_0,X37), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.53  fof(c_0_39, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.20/0.53  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.53  fof(c_0_41, plain, ![X38, X39]:k4_xboole_0(X38,k4_xboole_0(X38,X39))=k3_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.53  cnf(c_0_42, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_34])).
% 0.20/0.53  cnf(c_0_43, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.53  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.53  cnf(c_0_45, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.53  fof(c_0_46, plain, ![X43]:k5_xboole_0(X43,k1_xboole_0)=X43, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.20/0.53  fof(c_0_47, plain, ![X82, X83]:(((~m1_subset_1(X83,X82)|r2_hidden(X83,X82)|v1_xboole_0(X82))&(~r2_hidden(X83,X82)|m1_subset_1(X83,X82)|v1_xboole_0(X82)))&((~m1_subset_1(X83,X82)|v1_xboole_0(X83)|~v1_xboole_0(X82))&(~v1_xboole_0(X83)|m1_subset_1(X83,X82)|~v1_xboole_0(X82)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.20/0.53  fof(c_0_48, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))&k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.20/0.53  fof(c_0_49, plain, ![X89]:~v1_xboole_0(k1_zfmisc_1(X89)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.20/0.53  cnf(c_0_50, plain, (r2_hidden(X1,X2)|X3!=k5_xboole_0(X2,k3_xboole_0(X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_40, c_0_31])).
% 0.20/0.53  cnf(c_0_51, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.53  cnf(c_0_52, plain, (~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k1_zfmisc_1(X1))))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.53  cnf(c_0_53, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.53  cnf(c_0_54, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.53  fof(c_0_55, plain, ![X28, X29]:((~r2_hidden(esk3_2(X28,X29),X28)|~r2_hidden(esk3_2(X28,X29),X29)|X28=X29)&(r2_hidden(esk3_2(X28,X29),X28)|r2_hidden(esk3_2(X28,X29),X29)|X28=X29)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.20/0.53  cnf(c_0_56, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.53  cnf(c_0_57, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.53  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.53  cnf(c_0_59, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.53  cnf(c_0_60, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.53  cnf(c_0_61, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_31]), c_0_31])).
% 0.20/0.53  cnf(c_0_62, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.20/0.53  cnf(c_0_63, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk3_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.53  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_56])).
% 0.20/0.53  cnf(c_0_65, negated_conjecture, (r2_hidden(esk6_0,k1_zfmisc_1(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.20/0.53  fof(c_0_66, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.53  cnf(c_0_67, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.53  cnf(c_0_68, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.53  fof(c_0_69, plain, ![X80, X81]:k3_tarski(k2_tarski(X80,X81))=k2_xboole_0(X80,X81), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.20/0.53  fof(c_0_70, plain, ![X46, X47]:k1_enumset1(X46,X46,X47)=k2_tarski(X46,X47), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.53  cnf(c_0_71, negated_conjecture, (r1_tarski(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.53  cnf(c_0_72, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.53  fof(c_0_73, plain, ![X85, X86]:(~m1_subset_1(X86,k1_zfmisc_1(X85))|k3_subset_1(X85,X86)=k4_xboole_0(X85,X86)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.20/0.53  cnf(c_0_74, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.53  fof(c_0_75, plain, ![X40, X41, X42]:k4_xboole_0(X40,k4_xboole_0(X41,X42))=k2_xboole_0(k4_xboole_0(X40,X41),k3_xboole_0(X40,X42)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.20/0.53  cnf(c_0_76, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.20/0.53  cnf(c_0_77, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.53  fof(c_0_78, plain, ![X48, X49, X50]:k2_enumset1(X48,X48,X49,X50)=k1_enumset1(X48,X49,X50), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.53  fof(c_0_79, plain, ![X51, X52, X53, X54]:k3_enumset1(X51,X51,X52,X53,X54)=k2_enumset1(X51,X52,X53,X54), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.53  fof(c_0_80, plain, ![X55, X56, X57, X58, X59]:k4_enumset1(X55,X55,X56,X57,X58,X59)=k3_enumset1(X55,X56,X57,X58,X59), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.53  fof(c_0_81, plain, ![X60, X61, X62, X63, X64, X65]:k5_enumset1(X60,X60,X61,X62,X63,X64,X65)=k4_enumset1(X60,X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.53  fof(c_0_82, plain, ![X66, X67, X68, X69, X70, X71, X72]:k6_enumset1(X66,X66,X67,X68,X69,X70,X71,X72)=k5_enumset1(X66,X67,X68,X69,X70,X71,X72), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.53  fof(c_0_83, plain, ![X44, X45]:k2_xboole_0(X44,X45)=k5_xboole_0(X44,k4_xboole_0(X45,X44)), inference(variable_rename,[status(thm)],[t98_xboole_1])).
% 0.20/0.53  cnf(c_0_84, negated_conjecture, (k3_xboole_0(esk5_0,esk6_0)=esk6_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_71]), c_0_72])).
% 0.20/0.53  fof(c_0_85, plain, ![X87, X88]:(~m1_subset_1(X88,k1_zfmisc_1(X87))|m1_subset_1(k3_subset_1(X87,X88),k1_zfmisc_1(X87))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.20/0.53  cnf(c_0_86, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.53  cnf(c_0_87, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(X1,X2)),k5_xboole_0(X3,k3_xboole_0(X3,X1)))), inference(spm,[status(thm)],[c_0_42, c_0_74])).
% 0.20/0.53  cnf(c_0_88, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.53  cnf(c_0_89, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.53  cnf(c_0_90, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.53  cnf(c_0_91, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.20/0.53  cnf(c_0_92, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.53  cnf(c_0_93, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.20/0.53  cnf(c_0_94, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.53  cnf(c_0_95, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(X1,k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.20/0.53  cnf(c_0_96, negated_conjecture, (k5_xboole_0(esk5_0,k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0)))=esk6_0), inference(spm,[status(thm)],[c_0_61, c_0_84])).
% 0.20/0.53  fof(c_0_97, plain, ![X90, X91, X92]:(~m1_subset_1(X91,k1_zfmisc_1(X90))|~m1_subset_1(X92,k1_zfmisc_1(X90))|k4_subset_1(X90,X91,X92)=k2_xboole_0(X91,X92)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.20/0.53  cnf(c_0_98, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.20/0.53  cnf(c_0_99, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_86, c_0_31])).
% 0.20/0.53  cnf(c_0_100, negated_conjecture, (k3_xboole_0(esk6_0,X1)=k1_xboole_0|~r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(esk6_0,X1)),k5_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_87, c_0_84])).
% 0.20/0.53  cnf(c_0_101, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))))=k3_tarski(k6_enumset1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_31]), c_0_31]), c_0_31]), c_0_31]), c_0_90]), c_0_91]), c_0_92]), c_0_93]), c_0_94])).
% 0.20/0.53  cnf(c_0_102, plain, (k3_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_44, c_0_36])).
% 0.20/0.53  cnf(c_0_103, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_89]), c_0_31]), c_0_90]), c_0_91]), c_0_92]), c_0_93]), c_0_94])).
% 0.20/0.53  cnf(c_0_104, negated_conjecture, (k3_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0))=k5_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_96]), c_0_84])).
% 0.20/0.53  cnf(c_0_105, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_72])).
% 0.20/0.53  fof(c_0_106, plain, ![X84]:k2_subset_1(X84)=X84, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.53  cnf(c_0_107, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.20/0.53  cnf(c_0_108, negated_conjecture, (m1_subset_1(k3_subset_1(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_98, c_0_58])).
% 0.20/0.53  cnf(c_0_109, negated_conjecture, (k3_subset_1(esk5_0,esk6_0)=k5_xboole_0(esk5_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_58]), c_0_84])).
% 0.20/0.53  cnf(c_0_110, negated_conjecture, (k3_xboole_0(X1,esk6_0)=k1_xboole_0|~r2_hidden(esk3_2(k1_xboole_0,k3_xboole_0(X1,esk6_0)),k5_xboole_0(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_100, c_0_72])).
% 0.20/0.53  cnf(c_0_111, plain, (k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2))=k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_61])).
% 0.20/0.53  cnf(c_0_112, negated_conjecture, (k5_xboole_0(esk5_0,k5_xboole_0(esk5_0,esk6_0))=esk6_0), inference(rw,[status(thm)],[c_0_96, c_0_104])).
% 0.20/0.53  cnf(c_0_113, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_105]), c_0_54]), c_0_102])).
% 0.20/0.53  cnf(c_0_114, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=k2_subset_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.53  cnf(c_0_115, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.20/0.53  cnf(c_0_116, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_89]), c_0_90]), c_0_91]), c_0_92]), c_0_93]), c_0_94])).
% 0.20/0.53  cnf(c_0_117, negated_conjecture, (m1_subset_1(k5_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk5_0))), inference(rw,[status(thm)],[c_0_108, c_0_109])).
% 0.20/0.53  cnf(c_0_118, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_103, c_0_72])).
% 0.20/0.53  cnf(c_0_119, negated_conjecture, (k3_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_74]), c_0_72])).
% 0.20/0.53  cnf(c_0_120, negated_conjecture, (k5_xboole_0(esk6_0,k5_xboole_0(esk5_0,esk6_0))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_104]), c_0_112]), c_0_72]), c_0_104]), c_0_113]), c_0_105]), c_0_54])).
% 0.20/0.53  cnf(c_0_121, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k3_subset_1(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_114, c_0_115])).
% 0.20/0.53  cnf(c_0_122, negated_conjecture, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(esk5_0,esk6_0)))=k4_subset_1(esk5_0,X1,k5_xboole_0(esk5_0,esk6_0))|~m1_subset_1(X1,k1_zfmisc_1(esk5_0))), inference(spm,[status(thm)],[c_0_116, c_0_117])).
% 0.20/0.53  cnf(c_0_123, negated_conjecture, (k3_tarski(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,k5_xboole_0(esk5_0,esk6_0)))=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_54]), c_0_120])).
% 0.20/0.53  cnf(c_0_124, negated_conjecture, (k4_subset_1(esk5_0,esk6_0,k5_xboole_0(esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_121, c_0_109])).
% 0.20/0.53  cnf(c_0_125, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_58]), c_0_123]), c_0_124]), ['proof']).
% 0.20/0.53  # SZS output end CNFRefutation
% 0.20/0.53  # Proof object total steps             : 126
% 0.20/0.53  # Proof object clause steps            : 73
% 0.20/0.53  # Proof object formula steps           : 53
% 0.20/0.53  # Proof object conjectures             : 23
% 0.20/0.53  # Proof object clause conjectures      : 20
% 0.20/0.53  # Proof object formula conjectures     : 3
% 0.20/0.53  # Proof object initial clauses used    : 29
% 0.20/0.53  # Proof object initial formulas used   : 26
% 0.20/0.53  # Proof object generating inferences   : 27
% 0.20/0.53  # Proof object simplifying inferences  : 58
% 0.20/0.53  # Training examples: 0 positive, 0 negative
% 0.20/0.53  # Parsed axioms                        : 27
% 0.20/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.53  # Initial clauses                      : 47
% 0.20/0.53  # Removed in clause preprocessing      : 9
% 0.20/0.53  # Initial clauses in saturation        : 38
% 0.20/0.53  # Processed clauses                    : 1535
% 0.20/0.53  # ...of these trivial                  : 72
% 0.20/0.53  # ...subsumed                          : 1035
% 0.20/0.53  # ...remaining for further processing  : 428
% 0.20/0.53  # Other redundant clauses eliminated   : 10
% 0.20/0.53  # Clauses deleted for lack of memory   : 0
% 0.20/0.53  # Backward-subsumed                    : 0
% 0.20/0.53  # Backward-rewritten                   : 27
% 0.20/0.53  # Generated clauses                    : 6101
% 0.20/0.53  # ...of the previous two non-trivial   : 5525
% 0.20/0.53  # Contextual simplify-reflections      : 1
% 0.20/0.53  # Paramodulations                      : 6055
% 0.20/0.53  # Factorizations                       : 36
% 0.20/0.53  # Equation resolutions                 : 10
% 0.20/0.53  # Propositional unsat checks           : 0
% 0.20/0.53  #    Propositional check models        : 0
% 0.20/0.53  #    Propositional check unsatisfiable : 0
% 0.20/0.53  #    Propositional clauses             : 0
% 0.20/0.53  #    Propositional clauses after purity: 0
% 0.20/0.53  #    Propositional unsat core size     : 0
% 0.20/0.53  #    Propositional preprocessing time  : 0.000
% 0.20/0.53  #    Propositional encoding time       : 0.000
% 0.20/0.53  #    Propositional solver time         : 0.000
% 0.20/0.53  #    Success case prop preproc time    : 0.000
% 0.20/0.53  #    Success case prop encoding time   : 0.000
% 0.20/0.53  #    Success case prop solver time     : 0.000
% 0.20/0.53  # Current number of processed clauses  : 354
% 0.20/0.53  #    Positive orientable unit clauses  : 69
% 0.20/0.53  #    Positive unorientable unit clauses: 3
% 0.20/0.53  #    Negative unit clauses             : 37
% 0.20/0.53  #    Non-unit-clauses                  : 245
% 0.20/0.53  # Current number of unprocessed clauses: 4039
% 0.20/0.53  # ...number of literals in the above   : 13066
% 0.20/0.53  # Current number of archived formulas  : 0
% 0.20/0.53  # Current number of archived clauses   : 73
% 0.20/0.53  # Clause-clause subsumption calls (NU) : 6215
% 0.20/0.53  # Rec. Clause-clause subsumption calls : 4379
% 0.20/0.53  # Non-unit clause-clause subsumptions  : 481
% 0.20/0.53  # Unit Clause-clause subsumption calls : 1087
% 0.20/0.53  # Rewrite failures with RHS unbound    : 0
% 0.20/0.53  # BW rewrite match attempts            : 166
% 0.20/0.53  # BW rewrite match successes           : 33
% 0.20/0.53  # Condensation attempts                : 0
% 0.20/0.53  # Condensation successes               : 0
% 0.20/0.53  # Termbank termtop insertions          : 106640
% 0.20/0.53  
% 0.20/0.53  # -------------------------------------------------
% 0.20/0.53  # User time                : 0.179 s
% 0.20/0.53  # System time              : 0.005 s
% 0.20/0.53  # Total time               : 0.185 s
% 0.20/0.53  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
