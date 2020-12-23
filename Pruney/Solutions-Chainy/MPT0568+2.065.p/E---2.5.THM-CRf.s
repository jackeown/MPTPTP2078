%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:25 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 266 expanded)
%              Number of clauses        :   28 ( 106 expanded)
%              Number of leaves         :   17 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          :  129 ( 353 expanded)
%              Number of equality atoms :   59 ( 261 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(c_0_17,plain,(
    ! [X54,X55] : k1_setfam_1(k2_tarski(X54,X55)) = k3_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_18,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X9,X10] : k4_xboole_0(X9,X10) = k5_xboole_0(X9,k3_xboole_0(X9,X10)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_20,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,plain,(
    ! [X51,X52,X53] :
      ( ( r2_hidden(X51,X52)
        | ~ r2_hidden(X51,k4_xboole_0(X52,k1_tarski(X53))) )
      & ( X51 != X53
        | ~ r2_hidden(X51,k4_xboole_0(X52,k1_tarski(X53))) )
      & ( ~ r2_hidden(X51,X52)
        | X51 = X53
        | r2_hidden(X51,k4_xboole_0(X52,k1_tarski(X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_29,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_30,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39] : k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39) = k5_enumset1(X33,X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

fof(c_0_32,plain,(
    ! [X40,X41,X42,X44,X45,X46,X47,X49] :
      ( ( r2_hidden(X42,esk1_3(X40,X41,X42))
        | ~ r2_hidden(X42,X41)
        | X41 != k3_tarski(X40) )
      & ( r2_hidden(esk1_3(X40,X41,X42),X40)
        | ~ r2_hidden(X42,X41)
        | X41 != k3_tarski(X40) )
      & ( ~ r2_hidden(X44,X45)
        | ~ r2_hidden(X45,X40)
        | r2_hidden(X44,X41)
        | X41 != k3_tarski(X40) )
      & ( ~ r2_hidden(esk2_2(X46,X47),X47)
        | ~ r2_hidden(esk2_2(X46,X47),X49)
        | ~ r2_hidden(X49,X46)
        | X47 = k3_tarski(X46) )
      & ( r2_hidden(esk2_2(X46,X47),esk3_2(X46,X47))
        | r2_hidden(esk2_2(X46,X47),X47)
        | X47 = k3_tarski(X46) )
      & ( r2_hidden(esk3_2(X46,X47),X46)
        | r2_hidden(esk2_2(X46,X47),X47)
        | X47 = k3_tarski(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_33,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_41,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_42,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_43,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_44,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_21]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_40]),c_0_40])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X11] : k5_xboole_0(X11,X11) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_48,plain,(
    ! [X64,X65,X66,X68] :
      ( ( r2_hidden(esk7_3(X64,X65,X66),k2_relat_1(X66))
        | ~ r2_hidden(X64,k10_relat_1(X66,X65))
        | ~ v1_relat_1(X66) )
      & ( r2_hidden(k4_tarski(X64,esk7_3(X64,X65,X66)),X66)
        | ~ r2_hidden(X64,k10_relat_1(X66,X65))
        | ~ v1_relat_1(X66) )
      & ( r2_hidden(esk7_3(X64,X65,X66),X65)
        | ~ r2_hidden(X64,k10_relat_1(X66,X65))
        | ~ v1_relat_1(X66) )
      & ( ~ r2_hidden(X68,k2_relat_1(X66))
        | ~ r2_hidden(k4_tarski(X64,X68),X66)
        | ~ r2_hidden(X68,X65)
        | r2_hidden(X64,k10_relat_1(X66,X65))
        | ~ v1_relat_1(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_49,plain,(
    ! [X56,X57,X60,X62,X63] :
      ( ( ~ v1_relat_1(X56)
        | ~ r2_hidden(X57,X56)
        | X57 = k4_tarski(esk4_2(X56,X57),esk5_2(X56,X57)) )
      & ( r2_hidden(esk6_1(X60),X60)
        | v1_relat_1(X60) )
      & ( esk6_1(X60) != k4_tarski(X62,X63)
        | v1_relat_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_50,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk8_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),k1_xboole_0)
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_25]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])).

cnf(c_0_54,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r2_hidden(esk6_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,k10_relat_1(k1_xboole_0,esk8_0)),k10_relat_1(k1_xboole_0,esk8_0))
    | r2_hidden(esk3_2(k1_xboole_0,k10_relat_1(k1_xboole_0,esk8_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_59,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X1,X2,X3)),X3)
    | r2_hidden(esk6_1(X3),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_2(k1_xboole_0,k10_relat_1(k1_xboole_0,esk8_0)),k10_relat_1(k1_xboole_0,esk8_0)) ),
    inference(sr,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_58]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n012.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:27:07 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.45  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.17/0.45  # and selection function SelectNegativeLiterals.
% 0.17/0.45  #
% 0.17/0.45  # Preprocessing time       : 0.027 s
% 0.17/0.45  # Presaturation interreduction done
% 0.17/0.45  
% 0.17/0.45  # Proof found!
% 0.17/0.45  # SZS status Theorem
% 0.17/0.45  # SZS output start CNFRefutation
% 0.17/0.45  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.17/0.45  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.17/0.45  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.17/0.45  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.17/0.45  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.17/0.45  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.17/0.45  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.17/0.45  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.17/0.45  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.17/0.45  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.17/0.45  fof(t172_relat_1, conjecture, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 0.17/0.45  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.17/0.45  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.17/0.45  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.17/0.45  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.17/0.45  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.17/0.45  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.17/0.45  fof(c_0_17, plain, ![X54, X55]:k1_setfam_1(k2_tarski(X54,X55))=k3_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.17/0.45  fof(c_0_18, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.17/0.45  fof(c_0_19, plain, ![X9, X10]:k4_xboole_0(X9,X10)=k5_xboole_0(X9,k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.17/0.45  cnf(c_0_20, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.17/0.45  cnf(c_0_21, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.17/0.45  fof(c_0_22, plain, ![X51, X52, X53]:(((r2_hidden(X51,X52)|~r2_hidden(X51,k4_xboole_0(X52,k1_tarski(X53))))&(X51!=X53|~r2_hidden(X51,k4_xboole_0(X52,k1_tarski(X53)))))&(~r2_hidden(X51,X52)|X51=X53|r2_hidden(X51,k4_xboole_0(X52,k1_tarski(X53))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.17/0.45  fof(c_0_23, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.17/0.45  cnf(c_0_24, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.17/0.45  cnf(c_0_25, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.17/0.45  fof(c_0_26, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.17/0.45  fof(c_0_27, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.17/0.45  fof(c_0_28, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.17/0.45  fof(c_0_29, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.17/0.45  fof(c_0_30, plain, ![X33, X34, X35, X36, X37, X38, X39]:k6_enumset1(X33,X33,X34,X35,X36,X37,X38,X39)=k5_enumset1(X33,X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.17/0.45  fof(c_0_31, negated_conjecture, ~(![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t172_relat_1])).
% 0.17/0.45  fof(c_0_32, plain, ![X40, X41, X42, X44, X45, X46, X47, X49]:((((r2_hidden(X42,esk1_3(X40,X41,X42))|~r2_hidden(X42,X41)|X41!=k3_tarski(X40))&(r2_hidden(esk1_3(X40,X41,X42),X40)|~r2_hidden(X42,X41)|X41!=k3_tarski(X40)))&(~r2_hidden(X44,X45)|~r2_hidden(X45,X40)|r2_hidden(X44,X41)|X41!=k3_tarski(X40)))&((~r2_hidden(esk2_2(X46,X47),X47)|(~r2_hidden(esk2_2(X46,X47),X49)|~r2_hidden(X49,X46))|X47=k3_tarski(X46))&((r2_hidden(esk2_2(X46,X47),esk3_2(X46,X47))|r2_hidden(esk2_2(X46,X47),X47)|X47=k3_tarski(X46))&(r2_hidden(esk3_2(X46,X47),X46)|r2_hidden(esk2_2(X46,X47),X47)|X47=k3_tarski(X46))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.17/0.45  cnf(c_0_33, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.17/0.45  cnf(c_0_34, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.17/0.45  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.17/0.45  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.17/0.45  cnf(c_0_37, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.17/0.45  cnf(c_0_38, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.17/0.45  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.17/0.45  cnf(c_0_40, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.17/0.45  fof(c_0_41, plain, ![X8]:k3_xboole_0(X8,X8)=X8, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.17/0.45  fof(c_0_42, negated_conjecture, k10_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.17/0.45  cnf(c_0_43, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.17/0.45  cnf(c_0_44, plain, (r2_hidden(esk3_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.17/0.45  cnf(c_0_45, plain, (X1!=X2|~r2_hidden(X1,k5_xboole_0(X3,k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_21]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_40]), c_0_40])).
% 0.17/0.45  cnf(c_0_46, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.17/0.45  fof(c_0_47, plain, ![X11]:k5_xboole_0(X11,X11)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.17/0.45  fof(c_0_48, plain, ![X64, X65, X66, X68]:((((r2_hidden(esk7_3(X64,X65,X66),k2_relat_1(X66))|~r2_hidden(X64,k10_relat_1(X66,X65))|~v1_relat_1(X66))&(r2_hidden(k4_tarski(X64,esk7_3(X64,X65,X66)),X66)|~r2_hidden(X64,k10_relat_1(X66,X65))|~v1_relat_1(X66)))&(r2_hidden(esk7_3(X64,X65,X66),X65)|~r2_hidden(X64,k10_relat_1(X66,X65))|~v1_relat_1(X66)))&(~r2_hidden(X68,k2_relat_1(X66))|~r2_hidden(k4_tarski(X64,X68),X66)|~r2_hidden(X68,X65)|r2_hidden(X64,k10_relat_1(X66,X65))|~v1_relat_1(X66))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.17/0.45  fof(c_0_49, plain, ![X56, X57, X60, X62, X63]:((~v1_relat_1(X56)|(~r2_hidden(X57,X56)|X57=k4_tarski(esk4_2(X56,X57),esk5_2(X56,X57))))&((r2_hidden(esk6_1(X60),X60)|v1_relat_1(X60))&(esk6_1(X60)!=k4_tarski(X62,X63)|v1_relat_1(X60)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.17/0.45  cnf(c_0_50, negated_conjecture, (k10_relat_1(k1_xboole_0,esk8_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.17/0.45  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),k1_xboole_0)|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.17/0.45  cnf(c_0_52, plain, (~r2_hidden(X1,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))), inference(er,[status(thm)],[c_0_45])).
% 0.17/0.45  cnf(c_0_53, plain, (k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_25]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])).
% 0.17/0.45  cnf(c_0_54, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.17/0.45  cnf(c_0_55, plain, (r2_hidden(k4_tarski(X1,esk7_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.17/0.45  cnf(c_0_56, plain, (r2_hidden(esk6_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.45  cnf(c_0_57, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,k10_relat_1(k1_xboole_0,esk8_0)),k10_relat_1(k1_xboole_0,esk8_0))|r2_hidden(esk3_2(k1_xboole_0,k10_relat_1(k1_xboole_0,esk8_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.17/0.45  cnf(c_0_58, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.17/0.45  cnf(c_0_59, plain, (r2_hidden(k4_tarski(X1,esk7_3(X1,X2,X3)),X3)|r2_hidden(esk6_1(X3),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.17/0.45  cnf(c_0_60, negated_conjecture, (r2_hidden(esk2_2(k1_xboole_0,k10_relat_1(k1_xboole_0,esk8_0)),k10_relat_1(k1_xboole_0,esk8_0))), inference(sr,[status(thm)],[c_0_57, c_0_58])).
% 0.17/0.45  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_58]), c_0_58]), ['proof']).
% 0.17/0.45  # SZS output end CNFRefutation
% 0.17/0.45  # Proof object total steps             : 62
% 0.17/0.45  # Proof object clause steps            : 28
% 0.17/0.45  # Proof object formula steps           : 34
% 0.17/0.45  # Proof object conjectures             : 7
% 0.17/0.45  # Proof object clause conjectures      : 4
% 0.17/0.45  # Proof object formula conjectures     : 3
% 0.17/0.45  # Proof object initial clauses used    : 17
% 0.17/0.45  # Proof object initial formulas used   : 17
% 0.17/0.45  # Proof object generating inferences   : 5
% 0.17/0.45  # Proof object simplifying inferences  : 26
% 0.17/0.45  # Training examples: 0 positive, 0 negative
% 0.17/0.45  # Parsed axioms                        : 17
% 0.17/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.45  # Initial clauses                      : 29
% 0.17/0.45  # Removed in clause preprocessing      : 9
% 0.17/0.45  # Initial clauses in saturation        : 20
% 0.17/0.45  # Processed clauses                    : 457
% 0.17/0.45  # ...of these trivial                  : 2
% 0.17/0.45  # ...subsumed                          : 291
% 0.17/0.45  # ...remaining for further processing  : 164
% 0.17/0.45  # Other redundant clauses eliminated   : 79
% 0.17/0.45  # Clauses deleted for lack of memory   : 0
% 0.17/0.45  # Backward-subsumed                    : 2
% 0.17/0.45  # Backward-rewritten                   : 4
% 0.17/0.45  # Generated clauses                    : 5219
% 0.17/0.45  # ...of the previous two non-trivial   : 4738
% 0.17/0.45  # Contextual simplify-reflections      : 0
% 0.17/0.45  # Paramodulations                      : 5138
% 0.17/0.45  # Factorizations                       : 0
% 0.17/0.45  # Equation resolutions                 : 79
% 0.17/0.45  # Propositional unsat checks           : 0
% 0.17/0.45  #    Propositional check models        : 0
% 0.17/0.45  #    Propositional check unsatisfiable : 0
% 0.17/0.45  #    Propositional clauses             : 0
% 0.17/0.45  #    Propositional clauses after purity: 0
% 0.17/0.45  #    Propositional unsat core size     : 0
% 0.17/0.45  #    Propositional preprocessing time  : 0.000
% 0.17/0.45  #    Propositional encoding time       : 0.000
% 0.17/0.45  #    Propositional solver time         : 0.000
% 0.17/0.45  #    Success case prop preproc time    : 0.000
% 0.17/0.45  #    Success case prop encoding time   : 0.000
% 0.17/0.45  #    Success case prop solver time     : 0.000
% 0.17/0.45  # Current number of processed clauses  : 132
% 0.17/0.45  #    Positive orientable unit clauses  : 8
% 0.17/0.45  #    Positive unorientable unit clauses: 0
% 0.17/0.45  #    Negative unit clauses             : 3
% 0.17/0.45  #    Non-unit-clauses                  : 121
% 0.17/0.45  # Current number of unprocessed clauses: 4253
% 0.17/0.45  # ...number of literals in the above   : 19804
% 0.17/0.45  # Current number of archived formulas  : 0
% 0.17/0.45  # Current number of archived clauses   : 37
% 0.17/0.45  # Clause-clause subsumption calls (NU) : 3922
% 0.17/0.45  # Rec. Clause-clause subsumption calls : 3057
% 0.17/0.45  # Non-unit clause-clause subsumptions  : 253
% 0.17/0.45  # Unit Clause-clause subsumption calls : 11
% 0.17/0.45  # Rewrite failures with RHS unbound    : 0
% 0.17/0.45  # BW rewrite match attempts            : 1
% 0.17/0.45  # BW rewrite match successes           : 1
% 0.17/0.45  # Condensation attempts                : 0
% 0.17/0.45  # Condensation successes               : 0
% 0.17/0.45  # Termbank termtop insertions          : 107143
% 0.17/0.45  
% 0.17/0.45  # -------------------------------------------------
% 0.17/0.45  # User time                : 0.117 s
% 0.17/0.45  # System time              : 0.009 s
% 0.17/0.45  # Total time               : 0.126 s
% 0.17/0.45  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
