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
% DateTime   : Thu Dec  3 10:45:15 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 779 expanded)
%              Number of clauses        :   53 ( 328 expanded)
%              Number of leaves         :   24 ( 217 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 (1104 expanded)
%              Number of equality atoms :   89 ( 711 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t25_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

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

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d5_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k3_subset_1(X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(t94_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t39_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => k4_subset_1(X1,X2,k3_subset_1(X1,X2)) = k2_subset_1(X1) ) ),
    inference(assume_negation,[status(cth)],[t25_subset_1])).

fof(c_0_25,plain,(
    ! [X52,X53,X54,X55,X56,X57] :
      ( ( ~ r2_hidden(X54,X53)
        | r1_tarski(X54,X52)
        | X53 != k1_zfmisc_1(X52) )
      & ( ~ r1_tarski(X55,X52)
        | r2_hidden(X55,X53)
        | X53 != k1_zfmisc_1(X52) )
      & ( ~ r2_hidden(esk1_2(X56,X57),X57)
        | ~ r1_tarski(esk1_2(X56,X57),X56)
        | X57 = k1_zfmisc_1(X56) )
      & ( r2_hidden(esk1_2(X56,X57),X57)
        | r1_tarski(esk1_2(X56,X57),X56)
        | X57 = k1_zfmisc_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_26,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X62,X61)
        | r2_hidden(X62,X61)
        | v1_xboole_0(X61) )
      & ( ~ r2_hidden(X62,X61)
        | m1_subset_1(X62,X61)
        | v1_xboole_0(X61) )
      & ( ~ m1_subset_1(X62,X61)
        | v1_xboole_0(X62)
        | ~ v1_xboole_0(X61) )
      & ( ~ v1_xboole_0(X62)
        | m1_subset_1(X62,X61)
        | ~ v1_xboole_0(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    & k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_28,plain,(
    ! [X68] : ~ v1_xboole_0(k1_zfmisc_1(X68)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X59,X60] : k3_tarski(k2_tarski(X59,X60)) = k2_xboole_0(X59,X60) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_34,plain,(
    ! [X25,X26] : k1_enumset1(X25,X25,X26) = k2_tarski(X25,X26) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_35,plain,(
    ! [X64,X65] :
      ( ~ m1_subset_1(X65,k1_zfmisc_1(X64))
      | k3_subset_1(X64,X65) = k4_xboole_0(X64,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).

fof(c_0_36,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_37,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

fof(c_0_40,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_41,plain,(
    ! [X17,X18,X19] : k5_xboole_0(k5_xboole_0(X17,X18),X19) = k5_xboole_0(X17,k5_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

fof(c_0_42,plain,(
    ! [X20] : k5_xboole_0(X20,X20) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_43,plain,(
    ! [X69,X70,X71] :
      ( ~ m1_subset_1(X70,k1_zfmisc_1(X69))
      | ~ m1_subset_1(X71,k1_zfmisc_1(X69))
      | k4_subset_1(X69,X70,X71) = k2_xboole_0(X70,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_44,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_46,plain,(
    ! [X27,X28,X29] : k2_enumset1(X27,X27,X28,X29) = k1_enumset1(X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_47,plain,(
    ! [X30,X31,X32,X33] : k3_enumset1(X30,X30,X31,X32,X33) = k2_enumset1(X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_48,plain,(
    ! [X34,X35,X36,X37,X38] : k4_enumset1(X34,X34,X35,X36,X37,X38) = k3_enumset1(X34,X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_49,plain,(
    ! [X39,X40,X41,X42,X43,X44] : k5_enumset1(X39,X39,X40,X41,X42,X43,X44) = k4_enumset1(X39,X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_50,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] : k6_enumset1(X45,X45,X46,X47,X48,X49,X50,X51) = k5_enumset1(X45,X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_51,plain,(
    ! [X66,X67] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(X66))
      | m1_subset_1(k3_subset_1(X66,X67),k1_zfmisc_1(X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_52,plain,
    ( k3_subset_1(X2,X1) = k4_xboole_0(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_53,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_56,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_57,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k5_xboole_0(k5_xboole_0(X21,X22),k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t94_xboole_1])).

cnf(c_0_58,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_60,plain,(
    ! [X16] : k5_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

cnf(c_0_61,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_62,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_63,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_64,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_65,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_66,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_67,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_68,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_69,plain,
    ( k3_subset_1(X2,X1) = k5_xboole_0(X2,k3_xboole_0(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_70,negated_conjecture,
    ( k3_xboole_0(esk2_0,esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_71,plain,
    ( k2_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = k5_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( k4_subset_1(X2,X1,X3) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( k3_subset_1(esk2_0,esk3_0) = k5_xboole_0(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_31]),c_0_70])).

cnf(c_0_77,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_62]),c_0_63]),c_0_64]),c_0_65]),c_0_66]),c_0_67])).

cnf(c_0_78,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_59]),c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1)) = k4_subset_1(esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_31])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_81,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_77,c_0_58])).

fof(c_0_82,plain,(
    ! [X63] : k2_subset_1(X63) = X63 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_83,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[c_0_72,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))))) = k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_58])).

cnf(c_0_85,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != k2_subset_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_86,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_87,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_58])).

cnf(c_0_88,negated_conjecture,
    ( k5_xboole_0(esk3_0,k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))) = k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

fof(c_0_89,plain,(
    ! [X14,X15] : k2_xboole_0(X14,k4_xboole_0(X15,X14)) = k2_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t39_xboole_1])).

fof(c_0_90,plain,(
    ! [X23,X24] : k2_tarski(X23,X24) = k2_tarski(X24,X23) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_91,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_87]),c_0_73])).

cnf(c_0_93,negated_conjecture,
    ( k5_xboole_0(esk3_0,k5_xboole_0(k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)),X1)) = k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)),X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_88]),c_0_58]),c_0_58])).

cnf(c_0_94,plain,
    ( k2_xboole_0(X1,k4_xboole_0(X2,X1)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_95,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_76])).

cnf(c_0_97,negated_conjecture,
    ( k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)) = k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_92])).

cnf(c_0_98,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_62]),c_0_62]),c_0_53]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_65]),c_0_65]),c_0_66]),c_0_66]),c_0_67]),c_0_67])).

cnf(c_0_99,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_45]),c_0_45]),c_0_63]),c_0_63]),c_0_64]),c_0_64]),c_0_65]),c_0_65]),c_0_66]),c_0_66]),c_0_67]),c_0_67])).

cnf(c_0_100,negated_conjecture,
    ( k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))) != esk2_0 ),
    inference(rw,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_70]),c_0_81]),c_0_58]),c_0_84]),c_0_97]),c_0_99]),c_0_81]),c_0_70]),c_0_59]),c_0_73]),c_0_100]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:58:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.21/0.38  # and selection function SelectNegativeLiterals.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.028 s
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t25_subset_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 0.21/0.38  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.21/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.21/0.38  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.21/0.38  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.38  fof(d5_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k3_subset_1(X1,X2)=k4_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 0.21/0.38  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.21/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.21/0.38  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.38  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.21/0.38  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.21/0.38  fof(redefinition_k4_subset_1, axiom, ![X1, X2, X3]:((m1_subset_1(X2,k1_zfmisc_1(X1))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>k4_subset_1(X1,X2,X3)=k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 0.21/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.21/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.21/0.38  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.21/0.38  fof(dt_k3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 0.21/0.38  fof(t94_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 0.21/0.38  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.21/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.21/0.38  fof(t39_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 0.21/0.38  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.21/0.38  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k4_subset_1(X1,X2,k3_subset_1(X1,X2))=k2_subset_1(X1))), inference(assume_negation,[status(cth)],[t25_subset_1])).
% 0.21/0.38  fof(c_0_25, plain, ![X52, X53, X54, X55, X56, X57]:(((~r2_hidden(X54,X53)|r1_tarski(X54,X52)|X53!=k1_zfmisc_1(X52))&(~r1_tarski(X55,X52)|r2_hidden(X55,X53)|X53!=k1_zfmisc_1(X52)))&((~r2_hidden(esk1_2(X56,X57),X57)|~r1_tarski(esk1_2(X56,X57),X56)|X57=k1_zfmisc_1(X56))&(r2_hidden(esk1_2(X56,X57),X57)|r1_tarski(esk1_2(X56,X57),X56)|X57=k1_zfmisc_1(X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.21/0.38  fof(c_0_26, plain, ![X61, X62]:(((~m1_subset_1(X62,X61)|r2_hidden(X62,X61)|v1_xboole_0(X61))&(~r2_hidden(X62,X61)|m1_subset_1(X62,X61)|v1_xboole_0(X61)))&((~m1_subset_1(X62,X61)|v1_xboole_0(X62)|~v1_xboole_0(X61))&(~v1_xboole_0(X62)|m1_subset_1(X62,X61)|~v1_xboole_0(X61)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.21/0.38  fof(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))&k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.21/0.38  fof(c_0_28, plain, ![X68]:~v1_xboole_0(k1_zfmisc_1(X68)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.21/0.38  cnf(c_0_29, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_32, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.38  fof(c_0_33, plain, ![X59, X60]:k3_tarski(k2_tarski(X59,X60))=k2_xboole_0(X59,X60), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.38  fof(c_0_34, plain, ![X25, X26]:k1_enumset1(X25,X25,X26)=k2_tarski(X25,X26), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.38  fof(c_0_35, plain, ![X64, X65]:(~m1_subset_1(X65,k1_zfmisc_1(X64))|k3_subset_1(X64,X65)=k4_xboole_0(X64,X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_subset_1])])).
% 0.21/0.38  fof(c_0_36, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.21/0.38  fof(c_0_37, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.21/0.38  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_29])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.21/0.38  fof(c_0_40, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.38  fof(c_0_41, plain, ![X17, X18, X19]:k5_xboole_0(k5_xboole_0(X17,X18),X19)=k5_xboole_0(X17,k5_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.21/0.38  fof(c_0_42, plain, ![X20]:k5_xboole_0(X20,X20)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.21/0.38  fof(c_0_43, plain, ![X69, X70, X71]:(~m1_subset_1(X70,k1_zfmisc_1(X69))|~m1_subset_1(X71,k1_zfmisc_1(X69))|k4_subset_1(X69,X70,X71)=k2_xboole_0(X70,X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).
% 0.21/0.38  cnf(c_0_44, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.38  cnf(c_0_45, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.21/0.38  fof(c_0_46, plain, ![X27, X28, X29]:k2_enumset1(X27,X27,X28,X29)=k1_enumset1(X27,X28,X29), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.38  fof(c_0_47, plain, ![X30, X31, X32, X33]:k3_enumset1(X30,X30,X31,X32,X33)=k2_enumset1(X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.38  fof(c_0_48, plain, ![X34, X35, X36, X37, X38]:k4_enumset1(X34,X34,X35,X36,X37,X38)=k3_enumset1(X34,X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.21/0.38  fof(c_0_49, plain, ![X39, X40, X41, X42, X43, X44]:k5_enumset1(X39,X39,X40,X41,X42,X43,X44)=k4_enumset1(X39,X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.21/0.38  fof(c_0_50, plain, ![X45, X46, X47, X48, X49, X50, X51]:k6_enumset1(X45,X45,X46,X47,X48,X49,X50,X51)=k5_enumset1(X45,X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.21/0.38  fof(c_0_51, plain, ![X66, X67]:(~m1_subset_1(X67,k1_zfmisc_1(X66))|m1_subset_1(k3_subset_1(X66,X67),k1_zfmisc_1(X66))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).
% 0.21/0.38  cnf(c_0_52, plain, (k3_subset_1(X2,X1)=k4_xboole_0(X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.38  cnf(c_0_53, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.38  cnf(c_0_54, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.38  cnf(c_0_56, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.38  fof(c_0_57, plain, ![X21, X22]:k2_xboole_0(X21,X22)=k5_xboole_0(k5_xboole_0(X21,X22),k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t94_xboole_1])).
% 0.21/0.38  cnf(c_0_58, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.38  cnf(c_0_59, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.38  fof(c_0_60, plain, ![X16]:k5_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.21/0.38  cnf(c_0_61, plain, (k4_subset_1(X2,X1,X3)=k2_xboole_0(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~m1_subset_1(X3,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.38  cnf(c_0_62, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.38  cnf(c_0_63, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.38  cnf(c_0_64, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.38  cnf(c_0_65, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.38  cnf(c_0_66, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.38  cnf(c_0_67, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.38  cnf(c_0_68, plain, (m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.38  cnf(c_0_69, plain, (k3_subset_1(X2,X1)=k5_xboole_0(X2,k3_xboole_0(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.38  cnf(c_0_70, negated_conjecture, (k3_xboole_0(esk2_0,esk3_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.21/0.38  cnf(c_0_71, plain, (k2_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.38  cnf(c_0_72, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=k5_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.38  cnf(c_0_73, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.38  cnf(c_0_74, plain, (k4_subset_1(X2,X1,X3)=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67])).
% 0.21/0.38  cnf(c_0_75, negated_conjecture, (m1_subset_1(k3_subset_1(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_68, c_0_31])).
% 0.21/0.38  cnf(c_0_76, negated_conjecture, (k3_subset_1(esk2_0,esk3_0)=k5_xboole_0(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_31]), c_0_70])).
% 0.21/0.38  cnf(c_0_77, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_62]), c_0_63]), c_0_64]), c_0_65]), c_0_66]), c_0_67])).
% 0.21/0.38  cnf(c_0_78, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_59]), c_0_73])).
% 0.21/0.38  cnf(c_0_79, negated_conjecture, (k3_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1))=k4_subset_1(esk2_0,esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_74, c_0_31])).
% 0.21/0.38  cnf(c_0_80, negated_conjecture, (m1_subset_1(k5_xboole_0(esk2_0,esk3_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.21/0.38  cnf(c_0_81, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_77, c_0_58])).
% 0.21/0.38  fof(c_0_82, plain, ![X63]:k2_subset_1(X63)=X63, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.21/0.38  cnf(c_0_83, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[c_0_72, c_0_78])).
% 0.21/0.38  cnf(c_0_84, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))))=k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), c_0_58])).
% 0.21/0.38  cnf(c_0_85, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=k2_subset_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_86, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.21/0.38  cnf(c_0_87, plain, (k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_58])).
% 0.21/0.38  cnf(c_0_88, negated_conjecture, (k5_xboole_0(esk3_0,k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)))=k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0))))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.21/0.38  fof(c_0_89, plain, ![X14, X15]:k2_xboole_0(X14,k4_xboole_0(X15,X14))=k2_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t39_xboole_1])).
% 0.21/0.38  fof(c_0_90, plain, ![X23, X24]:k2_tarski(X23,X24)=k2_tarski(X24,X23), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.21/0.38  cnf(c_0_91, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k3_subset_1(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_85, c_0_86])).
% 0.21/0.38  cnf(c_0_92, plain, (k5_xboole_0(X1,k5_xboole_0(X2,X1))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_87]), c_0_73])).
% 0.21/0.38  cnf(c_0_93, negated_conjecture, (k5_xboole_0(esk3_0,k5_xboole_0(k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0)),X1))=k5_xboole_0(esk2_0,k5_xboole_0(esk3_0,k5_xboole_0(k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)),X1)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_88]), c_0_58]), c_0_58])).
% 0.21/0.38  cnf(c_0_94, plain, (k2_xboole_0(X1,k4_xboole_0(X2,X1))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.21/0.38  cnf(c_0_95, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.21/0.38  cnf(c_0_96, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))!=esk2_0), inference(rw,[status(thm)],[c_0_91, c_0_76])).
% 0.21/0.38  cnf(c_0_97, negated_conjecture, (k4_subset_1(esk2_0,esk3_0,k5_xboole_0(esk2_0,esk3_0))=k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_92])).
% 0.21/0.38  cnf(c_0_98, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))=k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_62]), c_0_62]), c_0_53]), c_0_63]), c_0_63]), c_0_64]), c_0_64]), c_0_65]), c_0_65]), c_0_66]), c_0_66]), c_0_67]), c_0_67])).
% 0.21/0.38  cnf(c_0_99, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_45]), c_0_45]), c_0_63]), c_0_63]), c_0_64]), c_0_64]), c_0_65]), c_0_65]), c_0_66]), c_0_66]), c_0_67]), c_0_67])).
% 0.21/0.38  cnf(c_0_100, negated_conjecture, (k5_xboole_0(esk2_0,k3_xboole_0(esk3_0,k5_xboole_0(esk2_0,esk3_0)))!=esk2_0), inference(rw,[status(thm)],[c_0_96, c_0_97])).
% 0.21/0.38  cnf(c_0_101, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_70]), c_0_81]), c_0_58]), c_0_84]), c_0_97]), c_0_99]), c_0_81]), c_0_70]), c_0_59]), c_0_73]), c_0_100]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 102
% 0.21/0.38  # Proof object clause steps            : 53
% 0.21/0.38  # Proof object formula steps           : 49
% 0.21/0.38  # Proof object conjectures             : 20
% 0.21/0.38  # Proof object clause conjectures      : 17
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 25
% 0.21/0.38  # Proof object initial formulas used   : 24
% 0.21/0.38  # Proof object generating inferences   : 16
% 0.21/0.38  # Proof object simplifying inferences  : 65
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 24
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 31
% 0.21/0.38  # Removed in clause preprocessing      : 9
% 0.21/0.38  # Initial clauses in saturation        : 22
% 0.21/0.38  # Processed clauses                    : 123
% 0.21/0.38  # ...of these trivial                  : 23
% 0.21/0.38  # ...subsumed                          : 12
% 0.21/0.38  # ...remaining for further processing  : 87
% 0.21/0.38  # Other redundant clauses eliminated   : 0
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 41
% 0.21/0.38  # Generated clauses                    : 270
% 0.21/0.38  # ...of the previous two non-trivial   : 247
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 257
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 13
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 46
% 0.21/0.38  #    Positive orientable unit clauses  : 20
% 0.21/0.38  #    Positive unorientable unit clauses: 3
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 21
% 0.21/0.38  # Current number of unprocessed clauses: 98
% 0.21/0.38  # ...number of literals in the above   : 156
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 50
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 56
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 54
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.21/0.38  # Unit Clause-clause subsumption calls : 46
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 59
% 0.21/0.38  # BW rewrite match successes           : 11
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 7295
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.034 s
% 0.21/0.38  # System time              : 0.005 s
% 0.21/0.38  # Total time               : 0.039 s
% 0.21/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
