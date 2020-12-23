%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:05 EST 2020

% Result     : Theorem 6.33s
% Output     : CNFRefutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :  169 (17957 expanded)
%              Number of clauses        :  124 (7719 expanded)
%              Number of leaves         :   22 (5020 expanded)
%              Depth                    :   33
%              Number of atoms          :  290 (28899 expanded)
%              Number of equality atoms :  176 (20461 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t22_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

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

fof(t120_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_22,plain,(
    ! [X83,X84,X85,X86] : k2_zfmisc_1(k3_xboole_0(X83,X84),k3_xboole_0(X85,X86)) = k3_xboole_0(k2_zfmisc_1(X83,X85),k2_zfmisc_1(X84,X86)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X12] : k3_xboole_0(X12,X12) = X12 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X25,X26] :
      ( ~ r1_tarski(X25,X26)
      | k3_xboole_0(X25,X26) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_28,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))
    & k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0
    & ( ~ r1_tarski(esk8_0,esk10_0)
      | ~ r1_tarski(esk9_0,esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_29,plain,(
    ! [X27,X28] :
      ( ( ~ r1_xboole_0(X27,X28)
        | k4_xboole_0(X27,X28) = X27 )
      & ( k4_xboole_0(X27,X28) != X27
        | r1_xboole_0(X27,X28) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_30,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k5_xboole_0(X21,k3_xboole_0(X21,X22)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_31,plain,(
    ! [X76,X77] : k3_tarski(k2_tarski(X76,X77)) = k2_xboole_0(X76,X77) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_32,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_33,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2)) = k2_zfmisc_1(k3_xboole_0(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X29] : k5_xboole_0(X29,X29) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_39,plain,(
    ! [X23,X24] : k2_xboole_0(X23,k3_xboole_0(X23,X24)) = X23 ),
    inference(variable_rename,[status(thm)],[t22_xboole_1])).

cnf(c_0_40,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_42,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_43,plain,(
    ! [X37,X38,X39,X40] : k3_enumset1(X37,X37,X38,X39,X40) = k2_enumset1(X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_44,plain,(
    ! [X41,X42,X43,X44,X45] : k4_enumset1(X41,X41,X42,X43,X44,X45) = k3_enumset1(X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_45,plain,(
    ! [X46,X47,X48,X49,X50,X51] : k5_enumset1(X46,X46,X47,X48,X49,X50,X51) = k4_enumset1(X46,X47,X48,X49,X50,X51) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_46,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58] : k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58) = k5_enumset1(X52,X53,X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X5,X3))) = k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X4,X5),X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_25]),c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_49,plain,(
    ! [X80,X81,X82] :
      ( k2_zfmisc_1(k2_xboole_0(X80,X81),X82) = k2_xboole_0(k2_zfmisc_1(X80,X82),k2_zfmisc_1(X81,X82))
      & k2_zfmisc_1(X82,k2_xboole_0(X80,X81)) = k2_xboole_0(k2_zfmisc_1(X82,X80),k2_zfmisc_1(X82,X81)) ) ),
    inference(variable_rename,[status(thm)],[t120_zfmisc_1])).

fof(c_0_50,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_51,plain,
    ( r1_xboole_0(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != X1 ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_52,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_53,plain,(
    ! [X78,X79] :
      ( ( k2_zfmisc_1(X78,X79) != k1_xboole_0
        | X78 = k1_xboole_0
        | X79 = k1_xboole_0 )
      & ( X78 != k1_xboole_0
        | k2_zfmisc_1(X78,X79) = k1_xboole_0 )
      & ( X79 != k1_xboole_0
        | k2_zfmisc_1(X78,X79) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_54,plain,(
    ! [X59,X60,X61,X62,X65,X66,X67,X68,X69,X70,X72,X73] :
      ( ( r2_hidden(esk3_4(X59,X60,X61,X62),X59)
        | ~ r2_hidden(X62,X61)
        | X61 != k2_zfmisc_1(X59,X60) )
      & ( r2_hidden(esk4_4(X59,X60,X61,X62),X60)
        | ~ r2_hidden(X62,X61)
        | X61 != k2_zfmisc_1(X59,X60) )
      & ( X62 = k4_tarski(esk3_4(X59,X60,X61,X62),esk4_4(X59,X60,X61,X62))
        | ~ r2_hidden(X62,X61)
        | X61 != k2_zfmisc_1(X59,X60) )
      & ( ~ r2_hidden(X66,X59)
        | ~ r2_hidden(X67,X60)
        | X65 != k4_tarski(X66,X67)
        | r2_hidden(X65,X61)
        | X61 != k2_zfmisc_1(X59,X60) )
      & ( ~ r2_hidden(esk5_3(X68,X69,X70),X70)
        | ~ r2_hidden(X72,X68)
        | ~ r2_hidden(X73,X69)
        | esk5_3(X68,X69,X70) != k4_tarski(X72,X73)
        | X70 = k2_zfmisc_1(X68,X69) )
      & ( r2_hidden(esk6_3(X68,X69,X70),X68)
        | r2_hidden(esk5_3(X68,X69,X70),X70)
        | X70 = k2_zfmisc_1(X68,X69) )
      & ( r2_hidden(esk7_3(X68,X69,X70),X69)
        | r2_hidden(esk5_3(X68,X69,X70),X70)
        | X70 = k2_zfmisc_1(X68,X69) )
      & ( esk5_3(X68,X69,X70) = k4_tarski(esk6_3(X68,X69,X70),esk7_3(X68,X69,X70))
        | r2_hidden(esk5_3(X68,X69,X70),X70)
        | X70 = k2_zfmisc_1(X68,X69) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_55,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_56,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_57,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_59,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_60,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,plain,
    ( k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_63,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk8_0,esk9_0)) = k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_26]),c_0_52])])).

cnf(c_0_67,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_69,plain,(
    ! [X87,X88,X89] :
      ( k2_zfmisc_1(k4_xboole_0(X87,X88),X89) = k4_xboole_0(k2_zfmisc_1(X87,X89),k2_zfmisc_1(X88,X89))
      & k2_zfmisc_1(X89,k4_xboole_0(X87,X88)) = k4_xboole_0(k2_zfmisc_1(X89,X87),k2_zfmisc_1(X89,X88)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

cnf(c_0_70,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk11_0)) = k2_zfmisc_1(esk8_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_60]),c_0_60]),c_0_61]),c_0_61])).

cnf(c_0_73,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_26])).

cnf(c_0_75,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_80,plain,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).

cnf(c_0_81,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])).

cnf(c_0_82,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
    | r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk5_3(X3,X4,k2_zfmisc_1(X1,X2))),X1)
    | r2_hidden(esk6_3(X3,X4,k2_zfmisc_1(X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_77,c_0_75])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_37]),c_0_37])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k3_xboole_0(k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))),X1)) = k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_79]),c_0_62])).

fof(c_0_85,plain,(
    ! [X19,X20] :
      ( ( k4_xboole_0(X19,X20) != k1_xboole_0
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | k4_xboole_0(X19,X20) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk5_3(k1_xboole_0,X3,X1)),k2_zfmisc_1(X4,X1))
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk6_3(X1,X2,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_82]),c_0_76]),c_0_76])).

cnf(c_0_88,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3))) = k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_83,c_0_62])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_26]),c_0_79])).

cnf(c_0_90,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X3 = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk5_3(k1_xboole_0,X4,X3)),k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k5_xboole_0(esk9_0,k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_52])).

cnf(c_0_94,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
    | r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk5_3(X3,X4,k2_zfmisc_1(X1,X2))),X1)
    | r2_hidden(esk7_3(X3,X4,k2_zfmisc_1(X1,X2)),X4) ),
    inference(spm,[status(thm)],[c_0_77,c_0_90])).

cnf(c_0_95,plain,
    ( k3_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X5,k3_xboole_0(X2,X4))) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X3),X2),k2_zfmisc_1(X5,X4)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_25]),c_0_25])).

cnf(c_0_96,plain,
    ( k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5))) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,k3_xboole_0(X4,X5))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_25]),c_0_25])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | k5_xboole_0(X1,k3_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_91,c_0_37])).

cnf(c_0_98,negated_conjecture,
    ( k5_xboole_0(esk9_0,k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))) = k1_xboole_0
    | k2_zfmisc_1(esk8_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_74])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk7_3(X1,X2,k1_xboole_0),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_94]),c_0_76]),c_0_76])).

cnf(c_0_100,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk9_0),k2_zfmisc_1(X1,esk11_0)) = k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_95,c_0_48])).

cnf(c_0_101,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),X1),k2_zfmisc_1(esk8_0,esk9_0)) = k3_xboole_0(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk10_0,k3_xboole_0(esk9_0,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_48])).

cnf(c_0_102,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))
    | k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3))) != k2_zfmisc_1(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_62]),c_0_88])).

cnf(c_0_103,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,X1) = k1_xboole_0
    | r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_104,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X3,esk7_3(X1,X2,k1_xboole_0)),k2_zfmisc_1(X4,X2))
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_80,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X2,k3_xboole_0(esk9_0,esk11_0)))) = k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),X2),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,k3_xboole_0(esk9_0,esk11_0))) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_101])).

fof(c_0_107,plain,(
    ! [X30,X31] : k2_tarski(X30,X31) = k2_tarski(X31,X30) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_108,plain,
    ( k2_zfmisc_1(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_109,negated_conjecture,
    ( r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))
    | r1_xboole_0(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk8_0,X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_103])).

cnf(c_0_110,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | k2_zfmisc_1(X3,X4) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk7_3(X3,X4,k1_xboole_0)),k2_zfmisc_1(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_87])).

cnf(c_0_111,plain,
    ( esk5_3(X1,X2,X3) = k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3))
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_112,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0)) = k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk10_0),esk11_0)) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_113,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_114,plain,
    ( k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3) = k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_56]),c_0_56]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_60]),c_0_60]),c_0_61]),c_0_61])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk8_0,k3_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_109]),c_0_62])).

cnf(c_0_116,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk5_3(X1,X2,k1_xboole_0),k2_zfmisc_1(X1,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_74])).

cnf(c_0_117,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_118,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk10_0),esk11_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_112]),c_0_25]),c_0_25]),c_0_48]),c_0_62]),c_0_26])).

cnf(c_0_119,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_41]),c_0_41]),c_0_57]),c_0_57]),c_0_58]),c_0_58]),c_0_59]),c_0_59]),c_0_60]),c_0_60]),c_0_61]),c_0_61])).

cnf(c_0_120,negated_conjecture,
    ( k2_zfmisc_1(k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0))),esk9_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_106]),c_0_114])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_26])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk5_3(esk8_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))),k1_xboole_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_79]),c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_118]),c_0_119]),c_0_114]),c_0_120])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_125,plain,
    ( k3_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(k3_xboole_0(X1,X3),X5)) = k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X4)),k2_zfmisc_1(X3,X5)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_25]),c_0_25])).

cnf(c_0_126,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk10_0),esk11_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_118,c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk10_0),esk11_0)) = k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk11_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_123]),c_0_63])).

cnf(c_0_128,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk5_3(esk8_0,k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))),k1_xboole_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_89]),c_0_117])).

cnf(c_0_130,negated_conjecture,
    ( k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_124])).

cnf(c_0_131,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)),k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0))) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0),k2_zfmisc_1(X1,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_71])).

cnf(c_0_132,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(X1,X2)),k2_zfmisc_1(esk10_0,k3_xboole_0(esk9_0,esk11_0))) = k3_xboole_0(k3_xboole_0(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk10_0,X2)),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_25])).

cnf(c_0_133,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk10_0,X1)) = k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),X1)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_48])).

cnf(c_0_134,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127]),c_0_71])).

cnf(c_0_135,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_128])).

cnf(c_0_136,negated_conjecture,
    ( r2_hidden(esk5_3(esk8_0,esk9_0,k1_xboole_0),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_137,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_138,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0),k2_zfmisc_1(esk10_0,esk11_0)) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk8_0),esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133]),c_0_33]),c_0_33])).

cnf(c_0_139,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk8_0),esk9_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_134]),c_0_106]),c_0_123]),c_0_133]),c_0_33]),c_0_33])).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(esk4_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_141,plain,
    ( k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3) = k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137,c_0_37]),c_0_37])).

cnf(c_0_142,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0),k2_zfmisc_1(esk10_0,esk11_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk4_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0))),k2_zfmisc_1(X2,esk9_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_80,c_0_140])).

cnf(c_0_144,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2)) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2) ),
    inference(rw,[status(thm)],[c_0_141,c_0_33])).

cnf(c_0_145,negated_conjecture,
    ( k2_zfmisc_1(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_142]),c_0_119]),c_0_114]),c_0_70])).

cnf(c_0_146,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk5_3(k1_xboole_0,X2,X1),esk4_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0))),k2_zfmisc_1(X1,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_143,c_0_81])).

cnf(c_0_147,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0))),esk9_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_145]),c_0_52])).

cnf(c_0_148,negated_conjecture,
    ( k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0))) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_74])).

cnf(c_0_149,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk8_0,esk9_0))
    | k5_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk11_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_97,c_0_63])).

cnf(c_0_150,plain,
    ( k5_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3))) = k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X4)),k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_25])).

cnf(c_0_151,negated_conjecture,
    ( r1_tarski(esk8_0,k3_xboole_0(esk8_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk8_0,esk9_0))
    | k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(esk8_0,esk10_0))),k3_xboole_0(esk9_0,esk11_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_149,c_0_150])).

cnf(c_0_153,negated_conjecture,
    ( k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_151])).

cnf(c_0_154,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_153]),c_0_52]),c_0_76])])).

cnf(c_0_155,negated_conjecture,
    ( r2_hidden(esk3_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_136])).

cnf(c_0_156,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,esk11_0)) = k2_zfmisc_1(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_154]),c_0_63]),c_0_71]),c_0_134])).

cnf(c_0_157,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk3_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0)),esk5_3(k1_xboole_0,X2,X1)),k2_zfmisc_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_155])).

cnf(c_0_158,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,k5_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_156]),c_0_52])).

cnf(c_0_159,negated_conjecture,
    ( k5_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_74])).

cnf(c_0_160,negated_conjecture,
    ( k5_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0))),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0)) = k2_zfmisc_1(k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),k3_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0))) ),
    inference(spm,[status(thm)],[c_0_150,c_0_106])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(esk9_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_159])).

cnf(c_0_162,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),k3_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0))) = k5_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0))),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_160,c_0_123])).

cnf(c_0_163,negated_conjecture,
    ( k3_xboole_0(esk9_0,esk11_0) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_161])).

cnf(c_0_164,negated_conjecture,
    ( k2_zfmisc_1(k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_162,c_0_163]),c_0_26]),c_0_163]),c_0_26]),c_0_52])).

cnf(c_0_165,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk10_0)
    | ~ r1_tarski(esk9_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_166,negated_conjecture,
    ( k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_164]),c_0_74])).

cnf(c_0_167,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_165,c_0_161])])).

cnf(c_0_168,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_166]),c_0_167]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 6.33/6.55  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 6.33/6.55  # and selection function GSelectMinInfpos.
% 6.33/6.55  #
% 6.33/6.55  # Preprocessing time       : 0.028 s
% 6.33/6.55  # Presaturation interreduction done
% 6.33/6.55  
% 6.33/6.55  # Proof found!
% 6.33/6.55  # SZS status Theorem
% 6.33/6.55  # SZS output start CNFRefutation
% 6.33/6.55  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 6.33/6.55  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.33/6.55  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 6.33/6.55  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.33/6.55  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.33/6.55  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.33/6.55  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.33/6.55  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.33/6.55  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.33/6.55  fof(t22_xboole_1, axiom, ![X1, X2]:k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 6.33/6.55  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.33/6.55  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.33/6.55  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.33/6.55  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.33/6.55  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 6.33/6.55  fof(t120_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k2_xboole_0(X1,X2))=k2_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 6.33/6.55  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.33/6.55  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.33/6.55  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.33/6.55  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 6.33/6.55  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.33/6.55  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.33/6.55  fof(c_0_22, plain, ![X83, X84, X85, X86]:k2_zfmisc_1(k3_xboole_0(X83,X84),k3_xboole_0(X85,X86))=k3_xboole_0(k2_zfmisc_1(X83,X85),k2_zfmisc_1(X84,X86)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 6.33/6.55  fof(c_0_23, plain, ![X12]:k3_xboole_0(X12,X12)=X12, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 6.33/6.55  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 6.33/6.55  cnf(c_0_25, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 6.33/6.55  cnf(c_0_26, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 6.33/6.55  fof(c_0_27, plain, ![X25, X26]:(~r1_tarski(X25,X26)|k3_xboole_0(X25,X26)=X25), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 6.33/6.55  fof(c_0_28, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))&(k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0&(~r1_tarski(esk8_0,esk10_0)|~r1_tarski(esk9_0,esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 6.33/6.55  fof(c_0_29, plain, ![X27, X28]:((~r1_xboole_0(X27,X28)|k4_xboole_0(X27,X28)=X27)&(k4_xboole_0(X27,X28)!=X27|r1_xboole_0(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 6.33/6.55  fof(c_0_30, plain, ![X21, X22]:k4_xboole_0(X21,X22)=k5_xboole_0(X21,k3_xboole_0(X21,X22)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 6.33/6.55  fof(c_0_31, plain, ![X76, X77]:k3_tarski(k2_tarski(X76,X77))=k2_xboole_0(X76,X77), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 6.33/6.55  fof(c_0_32, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.33/6.55  cnf(c_0_33, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))=k2_zfmisc_1(k3_xboole_0(X1,X3),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 6.33/6.55  cnf(c_0_34, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.33/6.55  cnf(c_0_35, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.33/6.55  cnf(c_0_36, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.33/6.55  cnf(c_0_37, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 6.33/6.55  fof(c_0_38, plain, ![X29]:k5_xboole_0(X29,X29)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 6.33/6.55  fof(c_0_39, plain, ![X23, X24]:k2_xboole_0(X23,k3_xboole_0(X23,X24))=X23, inference(variable_rename,[status(thm)],[t22_xboole_1])).
% 6.33/6.55  cnf(c_0_40, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 6.33/6.55  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 6.33/6.55  fof(c_0_42, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 6.33/6.55  fof(c_0_43, plain, ![X37, X38, X39, X40]:k3_enumset1(X37,X37,X38,X39,X40)=k2_enumset1(X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 6.33/6.55  fof(c_0_44, plain, ![X41, X42, X43, X44, X45]:k4_enumset1(X41,X41,X42,X43,X44,X45)=k3_enumset1(X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 6.33/6.55  fof(c_0_45, plain, ![X46, X47, X48, X49, X50, X51]:k5_enumset1(X46,X46,X47,X48,X49,X50,X51)=k4_enumset1(X46,X47,X48,X49,X50,X51), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 6.33/6.55  fof(c_0_46, plain, ![X52, X53, X54, X55, X56, X57, X58]:k6_enumset1(X52,X52,X53,X54,X55,X56,X57,X58)=k5_enumset1(X52,X53,X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 6.33/6.55  cnf(c_0_47, plain, (k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X4,X2),k2_zfmisc_1(X5,X3)))=k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X4,X5),X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_25]), c_0_25])).
% 6.33/6.55  cnf(c_0_48, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 6.33/6.55  fof(c_0_49, plain, ![X80, X81, X82]:(k2_zfmisc_1(k2_xboole_0(X80,X81),X82)=k2_xboole_0(k2_zfmisc_1(X80,X82),k2_zfmisc_1(X81,X82))&k2_zfmisc_1(X82,k2_xboole_0(X80,X81))=k2_xboole_0(k2_zfmisc_1(X82,X80),k2_zfmisc_1(X82,X81))), inference(variable_rename,[status(thm)],[t120_zfmisc_1])).
% 6.33/6.55  fof(c_0_50, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 6.33/6.55  cnf(c_0_51, plain, (r1_xboole_0(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=X1), inference(rw,[status(thm)],[c_0_36, c_0_37])).
% 6.33/6.55  cnf(c_0_52, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 6.33/6.55  fof(c_0_53, plain, ![X78, X79]:((k2_zfmisc_1(X78,X79)!=k1_xboole_0|(X78=k1_xboole_0|X79=k1_xboole_0))&((X78!=k1_xboole_0|k2_zfmisc_1(X78,X79)=k1_xboole_0)&(X79!=k1_xboole_0|k2_zfmisc_1(X78,X79)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 6.33/6.55  fof(c_0_54, plain, ![X59, X60, X61, X62, X65, X66, X67, X68, X69, X70, X72, X73]:(((((r2_hidden(esk3_4(X59,X60,X61,X62),X59)|~r2_hidden(X62,X61)|X61!=k2_zfmisc_1(X59,X60))&(r2_hidden(esk4_4(X59,X60,X61,X62),X60)|~r2_hidden(X62,X61)|X61!=k2_zfmisc_1(X59,X60)))&(X62=k4_tarski(esk3_4(X59,X60,X61,X62),esk4_4(X59,X60,X61,X62))|~r2_hidden(X62,X61)|X61!=k2_zfmisc_1(X59,X60)))&(~r2_hidden(X66,X59)|~r2_hidden(X67,X60)|X65!=k4_tarski(X66,X67)|r2_hidden(X65,X61)|X61!=k2_zfmisc_1(X59,X60)))&((~r2_hidden(esk5_3(X68,X69,X70),X70)|(~r2_hidden(X72,X68)|~r2_hidden(X73,X69)|esk5_3(X68,X69,X70)!=k4_tarski(X72,X73))|X70=k2_zfmisc_1(X68,X69))&(((r2_hidden(esk6_3(X68,X69,X70),X68)|r2_hidden(esk5_3(X68,X69,X70),X70)|X70=k2_zfmisc_1(X68,X69))&(r2_hidden(esk7_3(X68,X69,X70),X69)|r2_hidden(esk5_3(X68,X69,X70),X70)|X70=k2_zfmisc_1(X68,X69)))&(esk5_3(X68,X69,X70)=k4_tarski(esk6_3(X68,X69,X70),esk7_3(X68,X69,X70))|r2_hidden(esk5_3(X68,X69,X70),X70)|X70=k2_zfmisc_1(X68,X69))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 6.33/6.55  cnf(c_0_55, plain, (k2_xboole_0(X1,k3_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 6.33/6.55  cnf(c_0_56, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 6.33/6.55  cnf(c_0_57, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 6.33/6.55  cnf(c_0_58, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 6.33/6.55  cnf(c_0_59, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 6.33/6.55  cnf(c_0_60, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 6.33/6.55  cnf(c_0_61, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 6.33/6.55  cnf(c_0_62, plain, (k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))=k2_zfmisc_1(X1,k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 6.33/6.55  cnf(c_0_63, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk8_0,esk9_0))=k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk11_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 6.33/6.55  cnf(c_0_64, plain, (k2_zfmisc_1(X1,k2_xboole_0(X2,X3))=k2_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 6.33/6.55  cnf(c_0_65, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 6.33/6.55  cnf(c_0_66, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_26]), c_0_52])])).
% 6.33/6.55  cnf(c_0_67, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_53])).
% 6.33/6.55  cnf(c_0_68, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.33/6.55  fof(c_0_69, plain, ![X87, X88, X89]:(k2_zfmisc_1(k4_xboole_0(X87,X88),X89)=k4_xboole_0(k2_zfmisc_1(X87,X89),k2_zfmisc_1(X88,X89))&k2_zfmisc_1(X89,k4_xboole_0(X87,X88))=k4_xboole_0(k2_zfmisc_1(X89,X87),k2_zfmisc_1(X89,X88))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 6.33/6.55  cnf(c_0_70, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61])).
% 6.33/6.55  cnf(c_0_71, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk11_0))=k2_zfmisc_1(esk8_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 6.33/6.55  cnf(c_0_72, plain, (k2_zfmisc_1(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))=k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_56]), c_0_56]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_59]), c_0_59]), c_0_60]), c_0_60]), c_0_61]), c_0_61])).
% 6.33/6.55  cnf(c_0_73, plain, (r2_hidden(X5,X6)|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X5!=k4_tarski(X1,X3)|X6!=k2_zfmisc_1(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.33/6.55  cnf(c_0_74, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_26])).
% 6.33/6.55  cnf(c_0_75, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.33/6.55  cnf(c_0_76, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_67])).
% 6.33/6.55  cnf(c_0_77, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_68])).
% 6.33/6.55  cnf(c_0_78, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 6.33/6.55  cnf(c_0_79, negated_conjecture, (k2_zfmisc_1(esk8_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 6.33/6.55  cnf(c_0_80, plain, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))|~r2_hidden(X2,X4)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).
% 6.33/6.55  cnf(c_0_81, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])).
% 6.33/6.55  cnf(c_0_82, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)|r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk5_3(X3,X4,k2_zfmisc_1(X1,X2))),X1)|r2_hidden(esk6_3(X3,X4,k2_zfmisc_1(X1,X2)),X3)), inference(spm,[status(thm)],[c_0_77, c_0_75])).
% 6.33/6.55  cnf(c_0_83, plain, (k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))=k5_xboole_0(k2_zfmisc_1(X1,X2),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_37]), c_0_37])).
% 6.33/6.55  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk8_0,k3_xboole_0(k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))),X1))=k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_79]), c_0_62])).
% 6.33/6.55  fof(c_0_85, plain, ![X19, X20]:((k4_xboole_0(X19,X20)!=k1_xboole_0|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|k4_xboole_0(X19,X20)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 6.33/6.55  cnf(c_0_86, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(X2,esk5_3(k1_xboole_0,X3,X1)),k2_zfmisc_1(X4,X1))|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 6.33/6.55  cnf(c_0_87, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk6_3(X1,X2,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_82]), c_0_76]), c_0_76])).
% 6.33/6.55  cnf(c_0_88, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,k3_xboole_0(X2,X3)))=k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_83, c_0_62])).
% 6.33/6.55  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))))=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_26]), c_0_79])).
% 6.33/6.55  cnf(c_0_90, plain, (r2_hidden(esk7_3(X1,X2,X3),X2)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.33/6.55  cnf(c_0_91, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_85])).
% 6.33/6.55  cnf(c_0_92, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X3=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk5_3(k1_xboole_0,X4,X3)),k2_zfmisc_1(X1,X3))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 6.33/6.55  cnf(c_0_93, negated_conjecture, (k2_zfmisc_1(esk8_0,k5_xboole_0(esk9_0,k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_52])).
% 6.33/6.55  cnf(c_0_94, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)|r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk5_3(X3,X4,k2_zfmisc_1(X1,X2))),X1)|r2_hidden(esk7_3(X3,X4,k2_zfmisc_1(X1,X2)),X4)), inference(spm,[status(thm)],[c_0_77, c_0_90])).
% 6.33/6.55  cnf(c_0_95, plain, (k3_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(X5,k3_xboole_0(X2,X4)))=k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X3),X2),k2_zfmisc_1(X5,X4))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_25]), c_0_25])).
% 6.33/6.55  cnf(c_0_96, plain, (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X1,X2),X3),k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X5)))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,k3_xboole_0(X4,X5)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_25]), c_0_25])).
% 6.33/6.55  cnf(c_0_97, plain, (r1_tarski(X1,X2)|k5_xboole_0(X1,k3_xboole_0(X1,X2))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_91, c_0_37])).
% 6.33/6.55  cnf(c_0_98, negated_conjecture, (k5_xboole_0(esk9_0,k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))))=k1_xboole_0|k2_zfmisc_1(esk8_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_74])).
% 6.33/6.55  cnf(c_0_99, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk7_3(X1,X2,k1_xboole_0),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_94]), c_0_76]), c_0_76])).
% 6.33/6.55  cnf(c_0_100, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk9_0),k2_zfmisc_1(X1,esk11_0))=k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)))), inference(spm,[status(thm)],[c_0_95, c_0_48])).
% 6.33/6.55  cnf(c_0_101, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),X1),k2_zfmisc_1(esk8_0,esk9_0))=k3_xboole_0(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk10_0,k3_xboole_0(esk9_0,esk11_0)))), inference(spm,[status(thm)],[c_0_96, c_0_48])).
% 6.33/6.55  cnf(c_0_102, plain, (r1_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))|k2_zfmisc_1(X1,k5_xboole_0(X2,k3_xboole_0(X2,X3)))!=k2_zfmisc_1(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_62]), c_0_88])).
% 6.33/6.55  cnf(c_0_103, negated_conjecture, (k2_zfmisc_1(esk8_0,X1)=k1_xboole_0|r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 6.33/6.55  cnf(c_0_104, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X3,esk7_3(X1,X2,k1_xboole_0)),k2_zfmisc_1(X4,X2))|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_80, c_0_99])).
% 6.33/6.55  cnf(c_0_105, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(X2,k3_xboole_0(esk9_0,esk11_0))))=k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),X2),esk11_0))), inference(spm,[status(thm)],[c_0_47, c_0_100])).
% 6.33/6.55  cnf(c_0_106, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,k3_xboole_0(esk9_0,esk11_0)))=k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0)), inference(spm,[status(thm)],[c_0_33, c_0_101])).
% 6.33/6.55  fof(c_0_107, plain, ![X30, X31]:k2_tarski(X30,X31)=k2_tarski(X31,X30), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 6.33/6.55  cnf(c_0_108, plain, (k2_zfmisc_1(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 6.33/6.55  cnf(c_0_109, negated_conjecture, (r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))|r1_xboole_0(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk8_0,X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_103])).
% 6.33/6.55  cnf(c_0_110, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|k2_zfmisc_1(X3,X4)=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(X1,X2,k1_xboole_0),esk7_3(X3,X4,k1_xboole_0)),k2_zfmisc_1(X1,X4))), inference(spm,[status(thm)],[c_0_104, c_0_87])).
% 6.33/6.55  cnf(c_0_111, plain, (esk5_3(X1,X2,X3)=k4_tarski(esk6_3(X1,X2,X3),esk7_3(X1,X2,X3))|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.33/6.55  cnf(c_0_112, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0))=k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk10_0),esk11_0))), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 6.33/6.55  cnf(c_0_113, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 6.33/6.55  cnf(c_0_114, plain, (k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)),X3)=k3_tarski(k6_enumset1(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_56]), c_0_56]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_59]), c_0_59]), c_0_60]), c_0_60]), c_0_61]), c_0_61])).
% 6.33/6.55  cnf(c_0_115, negated_conjecture, (r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))|~r2_hidden(X1,k2_zfmisc_1(esk8_0,k3_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_109]), c_0_62])).
% 6.33/6.55  cnf(c_0_116, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|r2_hidden(esk5_3(X1,X2,k1_xboole_0),k2_zfmisc_1(X1,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_74])).
% 6.33/6.55  cnf(c_0_117, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.33/6.55  cnf(c_0_118, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk10_0),esk11_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_112]), c_0_25]), c_0_25]), c_0_48]), c_0_62]), c_0_26])).
% 6.33/6.55  cnf(c_0_119, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_41]), c_0_41]), c_0_57]), c_0_57]), c_0_58]), c_0_58]), c_0_59]), c_0_59]), c_0_60]), c_0_60]), c_0_61]), c_0_61])).
% 6.33/6.55  cnf(c_0_120, negated_conjecture, (k2_zfmisc_1(k3_tarski(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0))),esk9_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_106]), c_0_114])).
% 6.33/6.55  cnf(c_0_121, negated_conjecture, (r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))|~r2_hidden(X1,k2_zfmisc_1(esk8_0,X2))), inference(spm,[status(thm)],[c_0_115, c_0_26])).
% 6.33/6.55  cnf(c_0_122, negated_conjecture, (r2_hidden(esk5_3(esk8_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))),k1_xboole_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_79]), c_0_117])).
% 6.33/6.55  cnf(c_0_123, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_118]), c_0_119]), c_0_114]), c_0_120])).
% 6.33/6.55  cnf(c_0_124, negated_conjecture, (r1_tarski(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))), inference(spm,[status(thm)],[c_0_121, c_0_122])).
% 6.33/6.55  cnf(c_0_125, plain, (k3_xboole_0(k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)),k2_zfmisc_1(k3_xboole_0(X1,X3),X5))=k3_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X4)),k2_zfmisc_1(X3,X5))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_25]), c_0_25])).
% 6.33/6.55  cnf(c_0_126, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk10_0),esk11_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_118, c_0_123])).
% 6.33/6.55  cnf(c_0_127, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk10_0),esk11_0))=k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk11_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_123]), c_0_63])).
% 6.33/6.55  cnf(c_0_128, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 6.33/6.55  cnf(c_0_129, negated_conjecture, (r2_hidden(esk5_3(esk8_0,k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)))),k1_xboole_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_89]), c_0_117])).
% 6.33/6.55  cnf(c_0_130, negated_conjecture, (k3_xboole_0(esk9_0,k3_tarski(k6_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,esk9_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))))=esk9_0), inference(spm,[status(thm)],[c_0_34, c_0_124])).
% 6.33/6.55  cnf(c_0_131, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0)),k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)))=k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0),k2_zfmisc_1(X1,esk11_0))), inference(spm,[status(thm)],[c_0_95, c_0_71])).
% 6.33/6.55  cnf(c_0_132, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(X1,X2)),k2_zfmisc_1(esk10_0,k3_xboole_0(esk9_0,esk11_0)))=k3_xboole_0(k3_xboole_0(k2_zfmisc_1(esk8_0,X1),k2_zfmisc_1(esk10_0,X2)),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_101, c_0_25])).
% 6.33/6.55  cnf(c_0_133, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk10_0,X1))=k3_xboole_0(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),X1))), inference(spm,[status(thm)],[c_0_125, c_0_48])).
% 6.33/6.55  cnf(c_0_134, negated_conjecture, (k2_zfmisc_1(esk8_0,k3_xboole_0(k3_xboole_0(esk9_0,esk11_0),esk9_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_127]), c_0_71])).
% 6.33/6.55  cnf(c_0_135, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_128])).
% 6.33/6.55  cnf(c_0_136, negated_conjecture, (r2_hidden(esk5_3(esk8_0,esk9_0,k1_xboole_0),k2_zfmisc_1(esk8_0,esk9_0))), inference(rw,[status(thm)],[c_0_129, c_0_130])).
% 6.33/6.55  cnf(c_0_137, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 6.33/6.55  cnf(c_0_138, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0),k2_zfmisc_1(esk10_0,esk11_0))=k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk8_0),esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_133]), c_0_33]), c_0_33])).
% 6.33/6.55  cnf(c_0_139, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk8_0),esk9_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_134]), c_0_106]), c_0_123]), c_0_133]), c_0_33]), c_0_33])).
% 6.33/6.55  cnf(c_0_140, negated_conjecture, (r2_hidden(esk4_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0)),esk9_0)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 6.33/6.55  cnf(c_0_141, plain, (k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X3)=k5_xboole_0(k2_zfmisc_1(X1,X3),k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_137, c_0_37]), c_0_37])).
% 6.33/6.55  cnf(c_0_142, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0),k2_zfmisc_1(esk10_0,esk11_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[c_0_138, c_0_139])).
% 6.33/6.55  cnf(c_0_143, negated_conjecture, (r2_hidden(k4_tarski(X1,esk4_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0))),k2_zfmisc_1(X2,esk9_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_80, c_0_140])).
% 6.33/6.55  cnf(c_0_144, plain, (k5_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(k3_xboole_0(X1,X3),X2))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X3)),X2)), inference(rw,[status(thm)],[c_0_141, c_0_33])).
% 6.33/6.55  cnf(c_0_145, negated_conjecture, (k2_zfmisc_1(k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0)=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_142]), c_0_119]), c_0_114]), c_0_70])).
% 6.33/6.55  cnf(c_0_146, negated_conjecture, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk5_3(k1_xboole_0,X2,X1),esk4_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0))),k2_zfmisc_1(X1,esk9_0))), inference(spm,[status(thm)],[c_0_143, c_0_81])).
% 6.33/6.55  cnf(c_0_147, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0))),esk9_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144, c_0_145]), c_0_52])).
% 6.33/6.55  cnf(c_0_148, negated_conjecture, (k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_147]), c_0_74])).
% 6.33/6.55  cnf(c_0_149, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk8_0,esk9_0))|k5_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k3_xboole_0(k2_zfmisc_1(X1,esk9_0),k2_zfmisc_1(k3_xboole_0(esk8_0,esk10_0),esk11_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_97, c_0_63])).
% 6.33/6.55  cnf(c_0_150, plain, (k5_xboole_0(k2_zfmisc_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X4,X3)))=k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,X4)),k3_xboole_0(X2,X3))), inference(spm,[status(thm)],[c_0_144, c_0_25])).
% 6.33/6.55  cnf(c_0_151, negated_conjecture, (r1_tarski(esk8_0,k3_xboole_0(esk8_0,esk10_0))), inference(spm,[status(thm)],[c_0_97, c_0_148])).
% 6.33/6.55  cnf(c_0_152, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk8_0,esk9_0))|k2_zfmisc_1(k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(esk8_0,esk10_0))),k3_xboole_0(esk9_0,esk11_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_149, c_0_150])).
% 6.33/6.55  cnf(c_0_153, negated_conjecture, (k3_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0))=esk8_0), inference(spm,[status(thm)],[c_0_34, c_0_151])).
% 6.33/6.55  cnf(c_0_154, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,esk11_0)),k2_zfmisc_1(esk8_0,esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_153]), c_0_52]), c_0_76])])).
% 6.33/6.55  cnf(c_0_155, negated_conjecture, (r2_hidden(esk3_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0)),esk8_0)), inference(spm,[status(thm)],[c_0_77, c_0_136])).
% 6.33/6.55  cnf(c_0_156, negated_conjecture, (k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,esk11_0))=k2_zfmisc_1(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_154]), c_0_63]), c_0_71]), c_0_134])).
% 6.33/6.55  cnf(c_0_157, negated_conjecture, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk3_4(esk8_0,esk9_0,k2_zfmisc_1(esk8_0,esk9_0),esk5_3(esk8_0,esk9_0,k1_xboole_0)),esk5_3(k1_xboole_0,X2,X1)),k2_zfmisc_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_86, c_0_155])).
% 6.33/6.55  cnf(c_0_158, negated_conjecture, (k2_zfmisc_1(esk8_0,k5_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_156]), c_0_52])).
% 6.33/6.55  cnf(c_0_159, negated_conjecture, (k5_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_157, c_0_158]), c_0_74])).
% 6.33/6.55  cnf(c_0_160, negated_conjecture, (k5_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0))),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(esk8_0,esk10_0),esk8_0),esk9_0))=k2_zfmisc_1(k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),k3_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0)))), inference(spm,[status(thm)],[c_0_150, c_0_106])).
% 6.33/6.55  cnf(c_0_161, negated_conjecture, (r1_tarski(esk9_0,esk11_0)), inference(spm,[status(thm)],[c_0_97, c_0_159])).
% 6.33/6.55  cnf(c_0_162, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),k3_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0)))=k5_xboole_0(k2_zfmisc_1(esk8_0,k3_xboole_0(esk9_0,k3_xboole_0(esk9_0,esk11_0))),k2_zfmisc_1(esk8_0,esk9_0))), inference(rw,[status(thm)],[c_0_160, c_0_123])).
% 6.33/6.55  cnf(c_0_163, negated_conjecture, (k3_xboole_0(esk9_0,esk11_0)=esk9_0), inference(spm,[status(thm)],[c_0_34, c_0_161])).
% 6.33/6.55  cnf(c_0_164, negated_conjecture, (k2_zfmisc_1(k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0)),esk9_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_162, c_0_163]), c_0_26]), c_0_163]), c_0_26]), c_0_52])).
% 6.33/6.55  cnf(c_0_165, negated_conjecture, (~r1_tarski(esk8_0,esk10_0)|~r1_tarski(esk9_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.33/6.55  cnf(c_0_166, negated_conjecture, (k5_xboole_0(esk8_0,k3_xboole_0(esk8_0,esk10_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_164]), c_0_74])).
% 6.33/6.55  cnf(c_0_167, negated_conjecture, (~r1_tarski(esk8_0,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_165, c_0_161])])).
% 6.33/6.55  cnf(c_0_168, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_166]), c_0_167]), ['proof']).
% 6.33/6.55  # SZS output end CNFRefutation
% 6.33/6.55  # Proof object total steps             : 169
% 6.33/6.55  # Proof object clause steps            : 124
% 6.33/6.55  # Proof object formula steps           : 45
% 6.33/6.55  # Proof object conjectures             : 64
% 6.33/6.55  # Proof object clause conjectures      : 61
% 6.33/6.55  # Proof object formula conjectures     : 3
% 6.33/6.55  # Proof object initial clauses used    : 31
% 6.33/6.55  # Proof object initial formulas used   : 22
% 6.33/6.55  # Proof object generating inferences   : 69
% 6.33/6.55  # Proof object simplifying inferences  : 127
% 6.33/6.55  # Training examples: 0 positive, 0 negative
% 6.33/6.55  # Parsed axioms                        : 23
% 6.33/6.55  # Removed by relevancy pruning/SinE    : 0
% 6.33/6.55  # Initial clauses                      : 40
% 6.33/6.55  # Removed in clause preprocessing      : 8
% 6.33/6.55  # Initial clauses in saturation        : 32
% 6.33/6.55  # Processed clauses                    : 7774
% 6.33/6.55  # ...of these trivial                  : 111
% 6.33/6.55  # ...subsumed                          : 3444
% 6.33/6.55  # ...remaining for further processing  : 4219
% 6.33/6.55  # Other redundant clauses eliminated   : 20
% 6.33/6.55  # Clauses deleted for lack of memory   : 0
% 6.33/6.55  # Backward-subsumed                    : 356
% 6.33/6.55  # Backward-rewritten                   : 857
% 6.33/6.55  # Generated clauses                    : 563607
% 6.33/6.55  # ...of the previous two non-trivial   : 557112
% 6.33/6.55  # Contextual simplify-reflections      : 2
% 6.33/6.55  # Paramodulations                      : 563566
% 6.33/6.55  # Factorizations                       : 14
% 6.33/6.55  # Equation resolutions                 : 28
% 6.33/6.55  # Propositional unsat checks           : 0
% 6.33/6.55  #    Propositional check models        : 0
% 6.33/6.55  #    Propositional check unsatisfiable : 0
% 6.33/6.55  #    Propositional clauses             : 0
% 6.33/6.55  #    Propositional clauses after purity: 0
% 6.33/6.55  #    Propositional unsat core size     : 0
% 6.33/6.55  #    Propositional preprocessing time  : 0.000
% 6.33/6.55  #    Propositional encoding time       : 0.000
% 6.33/6.55  #    Propositional solver time         : 0.000
% 6.33/6.55  #    Success case prop preproc time    : 0.000
% 6.33/6.55  #    Success case prop encoding time   : 0.000
% 6.33/6.55  #    Success case prop solver time     : 0.000
% 6.33/6.55  # Current number of processed clauses  : 2968
% 6.33/6.55  #    Positive orientable unit clauses  : 323
% 6.33/6.55  #    Positive unorientable unit clauses: 5
% 6.33/6.55  #    Negative unit clauses             : 4
% 6.33/6.55  #    Non-unit-clauses                  : 2636
% 6.33/6.55  # Current number of unprocessed clauses: 539345
% 6.33/6.55  # ...number of literals in the above   : 2304660
% 6.33/6.55  # Current number of archived formulas  : 0
% 6.33/6.55  # Current number of archived clauses   : 1253
% 6.33/6.55  # Clause-clause subsumption calls (NU) : 363867
% 6.33/6.55  # Rec. Clause-clause subsumption calls : 97819
% 6.33/6.55  # Non-unit clause-clause subsumptions  : 2027
% 6.33/6.55  # Unit Clause-clause subsumption calls : 21777
% 6.33/6.55  # Rewrite failures with RHS unbound    : 0
% 6.33/6.55  # BW rewrite match attempts            : 25844
% 6.33/6.55  # BW rewrite match successes           : 161
% 6.33/6.55  # Condensation attempts                : 0
% 6.33/6.55  # Condensation successes               : 0
% 6.33/6.55  # Termbank termtop insertions          : 20969956
% 6.42/6.57  
% 6.42/6.57  # -------------------------------------------------
% 6.42/6.57  # User time                : 5.983 s
% 6.42/6.57  # System time              : 0.244 s
% 6.42/6.57  # Total time               : 6.228 s
% 6.42/6.57  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
