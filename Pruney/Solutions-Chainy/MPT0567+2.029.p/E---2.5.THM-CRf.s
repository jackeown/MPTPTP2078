%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 436 expanded)
%              Number of clauses        :   33 ( 197 expanded)
%              Number of leaves         :   14 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          :  146 (1427 expanded)
%              Number of equality atoms :   50 ( 185 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

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

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k10_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t171_relat_1])).

fof(c_0_15,plain,(
    ! [X58,X59,X60,X62] :
      ( ( r2_hidden(esk4_3(X58,X59,X60),k2_relat_1(X60))
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( r2_hidden(k4_tarski(X58,esk4_3(X58,X59,X60)),X60)
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( r2_hidden(esk4_3(X58,X59,X60),X59)
        | ~ r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) )
      & ( ~ r2_hidden(X62,k2_relat_1(X60))
        | ~ r2_hidden(k4_tarski(X58,X62),X60)
        | ~ r2_hidden(X62,X59)
        | r2_hidden(X58,k10_relat_1(X60,X59))
        | ~ v1_relat_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & k10_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X17,X18,X20,X21,X22] :
      ( ( r2_hidden(esk2_2(X17,X18),X17)
        | r1_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | r1_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X22,X21)
        | ~ r1_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_18,plain,(
    ! [X23] : r1_xboole_0(X23,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk5_0),X2)
    | ~ r2_hidden(X1,k10_relat_1(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(k10_relat_1(esk5_0,X1),X2)
    | r2_hidden(esk4_3(esk2_2(k10_relat_1(esk5_0,X1),X2),X1,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r1_xboole_0(k10_relat_1(esk5_0,X1),X2)
    | ~ r2_hidden(esk4_3(esk2_2(k10_relat_1(esk5_0,X1),X2),X1,esk5_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(k10_relat_1(esk5_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

fof(c_0_29,plain,(
    ! [X51,X52] :
      ( ~ r1_xboole_0(k1_tarski(X51),X52)
      | ~ r2_hidden(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_30,plain,(
    ! [X53,X54] :
      ( ( r2_hidden(esk3_2(X53,X54),X53)
        | X53 = k1_tarski(X54)
        | X53 = k1_xboole_0 )
      & ( esk3_2(X53,X54) != X54
        | X53 = k1_tarski(X54)
        | X53 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(X1,k10_relat_1(esk5_0,k1_xboole_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

fof(c_0_32,plain,(
    ! [X56,X57] : k1_setfam_1(k2_tarski(X56,X57)) = k3_xboole_0(X56,X57) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_33,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_34,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),k10_relat_1(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_38,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_39,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_41,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_42,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_43,plain,(
    ! [X33,X34,X35,X36,X37] : k4_enumset1(X33,X33,X34,X35,X36,X37) = k3_enumset1(X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_44,plain,(
    ! [X38,X39,X40,X41,X42,X43] : k5_enumset1(X38,X38,X39,X40,X41,X42,X43) = k4_enumset1(X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_45,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] : k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50) = k5_enumset1(X44,X45,X46,X47,X48,X49,X50) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_46,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | ~ r1_xboole_0(k1_tarski(esk3_2(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( r1_xboole_0(X1,k10_relat_1(esk5_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( k10_relat_1(esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( k1_tarski(X1) = k10_relat_1(esk5_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_57,plain,
    ( X3 = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_56]),c_0_28])])).

cnf(c_0_59,plain,
    ( X1 = k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_57,c_0_58]),c_0_58])).

cnf(c_0_60,plain,
    ( X1 = X2 ),
    inference(spm,[status(thm)],[c_0_59,c_0_59])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_48,c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S054N
% 0.20/0.40  # and selection function GSelectMinInfpos.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.045 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t171_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 0.20/0.40  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.20/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.20/0.40  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.20/0.40  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.20/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.40  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.20/0.40  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.20/0.40  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.20/0.40  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.20/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k1_xboole_0)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t171_relat_1])).
% 0.20/0.40  fof(c_0_15, plain, ![X58, X59, X60, X62]:((((r2_hidden(esk4_3(X58,X59,X60),k2_relat_1(X60))|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60))&(r2_hidden(k4_tarski(X58,esk4_3(X58,X59,X60)),X60)|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60)))&(r2_hidden(esk4_3(X58,X59,X60),X59)|~r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60)))&(~r2_hidden(X62,k2_relat_1(X60))|~r2_hidden(k4_tarski(X58,X62),X60)|~r2_hidden(X62,X59)|r2_hidden(X58,k10_relat_1(X60,X59))|~v1_relat_1(X60))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.20/0.40  fof(c_0_16, negated_conjecture, (v1_relat_1(esk5_0)&k10_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.40  fof(c_0_17, plain, ![X17, X18, X20, X21, X22]:(((r2_hidden(esk2_2(X17,X18),X17)|r1_xboole_0(X17,X18))&(r2_hidden(esk2_2(X17,X18),X18)|r1_xboole_0(X17,X18)))&(~r2_hidden(X22,X20)|~r2_hidden(X22,X21)|~r1_xboole_0(X20,X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.40  fof(c_0_18, plain, ![X23]:r1_xboole_0(X23,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.20/0.40  cnf(c_0_19, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_21, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_22, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk5_0),X2)|~r2_hidden(X1,k10_relat_1(esk5_0,X2))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.40  cnf(c_0_24, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  cnf(c_0_25, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (r1_xboole_0(k10_relat_1(esk5_0,X1),X2)|r2_hidden(esk4_3(esk2_2(k10_relat_1(esk5_0,X1),X2),X1,esk5_0),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.40  cnf(c_0_27, negated_conjecture, (r1_xboole_0(k10_relat_1(esk5_0,X1),X2)|~r2_hidden(esk4_3(esk2_2(k10_relat_1(esk5_0,X1),X2),X1,esk5_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (r1_xboole_0(k10_relat_1(esk5_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.40  fof(c_0_29, plain, ![X51, X52]:(~r1_xboole_0(k1_tarski(X51),X52)|~r2_hidden(X51,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.20/0.40  fof(c_0_30, plain, ![X53, X54]:((r2_hidden(esk3_2(X53,X54),X53)|(X53=k1_tarski(X54)|X53=k1_xboole_0))&(esk3_2(X53,X54)!=X54|(X53=k1_tarski(X54)|X53=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (~r2_hidden(X1,k10_relat_1(esk5_0,k1_xboole_0))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 0.20/0.40  fof(c_0_32, plain, ![X56, X57]:k1_setfam_1(k2_tarski(X56,X57))=k3_xboole_0(X56,X57), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.20/0.40  fof(c_0_33, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.40  cnf(c_0_34, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.40  cnf(c_0_35, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (r1_xboole_0(X1,X2)|~r2_hidden(esk2_2(X1,X2),k10_relat_1(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_31, c_0_24])).
% 0.20/0.40  cnf(c_0_37, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.40  fof(c_0_38, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:((((r2_hidden(X11,X8)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9))&(r2_hidden(X11,X9)|~r2_hidden(X11,X10)|X10!=k3_xboole_0(X8,X9)))&(~r2_hidden(X12,X8)|~r2_hidden(X12,X9)|r2_hidden(X12,X10)|X10!=k3_xboole_0(X8,X9)))&((~r2_hidden(esk1_3(X13,X14,X15),X15)|(~r2_hidden(esk1_3(X13,X14,X15),X13)|~r2_hidden(esk1_3(X13,X14,X15),X14))|X15=k3_xboole_0(X13,X14))&((r2_hidden(esk1_3(X13,X14,X15),X13)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))&(r2_hidden(esk1_3(X13,X14,X15),X14)|r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k3_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.40  cnf(c_0_39, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.40  cnf(c_0_40, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.40  fof(c_0_41, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.40  fof(c_0_42, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.20/0.40  fof(c_0_43, plain, ![X33, X34, X35, X36, X37]:k4_enumset1(X33,X33,X34,X35,X36,X37)=k3_enumset1(X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.20/0.40  fof(c_0_44, plain, ![X38, X39, X40, X41, X42, X43]:k5_enumset1(X38,X38,X39,X40,X41,X42,X43)=k4_enumset1(X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.20/0.40  fof(c_0_45, plain, ![X44, X45, X46, X47, X48, X49, X50]:k6_enumset1(X44,X44,X45,X46,X47,X48,X49,X50)=k5_enumset1(X44,X45,X46,X47,X48,X49,X50), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.20/0.40  cnf(c_0_46, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|~r1_xboole_0(k1_tarski(esk3_2(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (r1_xboole_0(X1,k10_relat_1(esk5_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.40  cnf(c_0_48, negated_conjecture, (k10_relat_1(esk5_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.40  cnf(c_0_49, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_50, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.40  cnf(c_0_51, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.40  cnf(c_0_52, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.40  cnf(c_0_53, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.40  cnf(c_0_54, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.40  cnf(c_0_55, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.40  cnf(c_0_56, negated_conjecture, (k1_tarski(X1)=k10_relat_1(esk5_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.20/0.40  cnf(c_0_57, plain, (X3=k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_53]), c_0_54]), c_0_55])).
% 0.20/0.40  cnf(c_0_58, plain, (~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_56]), c_0_28])])).
% 0.20/0.40  cnf(c_0_59, plain, (X1=k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_57, c_0_58]), c_0_58])).
% 0.20/0.40  cnf(c_0_60, plain, (X1=X2), inference(spm,[status(thm)],[c_0_59, c_0_59])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_48, c_0_60]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 62
% 0.20/0.40  # Proof object clause steps            : 33
% 0.20/0.40  # Proof object formula steps           : 29
% 0.20/0.40  # Proof object conjectures             : 14
% 0.20/0.40  # Proof object clause conjectures      : 11
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 17
% 0.20/0.40  # Proof object initial formulas used   : 14
% 0.20/0.40  # Proof object generating inferences   : 11
% 0.20/0.40  # Proof object simplifying inferences  : 14
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 14
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 26
% 0.20/0.40  # Removed in clause preprocessing      : 7
% 0.20/0.40  # Initial clauses in saturation        : 19
% 0.20/0.40  # Processed clauses                    : 95
% 0.20/0.40  # ...of these trivial                  : 4
% 0.20/0.40  # ...subsumed                          : 26
% 0.20/0.40  # ...remaining for further processing  : 65
% 0.20/0.40  # Other redundant clauses eliminated   : 9
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 10
% 0.20/0.40  # Backward-rewritten                   : 15
% 0.20/0.40  # Generated clauses                    : 311
% 0.20/0.40  # ...of the previous two non-trivial   : 240
% 0.20/0.40  # Contextual simplify-reflections      : 0
% 0.20/0.40  # Paramodulations                      : 269
% 0.20/0.40  # Factorizations                       : 29
% 0.20/0.40  # Equation resolutions                 : 9
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 14
% 0.20/0.40  #    Positive orientable unit clauses  : 2
% 0.20/0.40  #    Positive unorientable unit clauses: 1
% 0.20/0.40  #    Negative unit clauses             : 1
% 0.20/0.40  #    Non-unit-clauses                  : 10
% 0.20/0.40  # Current number of unprocessed clauses: 179
% 0.20/0.40  # ...number of literals in the above   : 554
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 55
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 135
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 105
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 15
% 0.20/0.40  # Unit Clause-clause subsumption calls : 39
% 0.20/0.40  # Rewrite failures with RHS unbound    : 108
% 0.20/0.40  # BW rewrite match attempts            : 69
% 0.20/0.40  # BW rewrite match successes           : 66
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 3853
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.050 s
% 0.20/0.40  # System time              : 0.009 s
% 0.20/0.40  # Total time               : 0.059 s
% 0.20/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
