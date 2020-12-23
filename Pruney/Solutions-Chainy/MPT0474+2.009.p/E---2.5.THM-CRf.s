%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:23 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 746 expanded)
%              Number of clauses        :   44 ( 302 expanded)
%              Number of leaves         :   19 ( 223 expanded)
%              Depth                    :   14
%              Number of atoms          :  156 (1060 expanded)
%              Number of equality atoms :   84 ( 783 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t93_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t101_xboole_1,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t41_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k6_subset_1(X1,X2)) = k6_subset_1(k4_relat_1(X1),k4_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t66_relat_1,conjecture,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

fof(c_0_19,plain,(
    ! [X42,X43] : k3_tarski(k2_tarski(X42,X43)) = k2_xboole_0(X42,X43) ),
    inference(variable_rename,[status(thm)],[t93_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X47,X48] : k1_setfam_1(k2_tarski(X47,X48)) = k3_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X16,X17] : k5_xboole_0(X16,X17) = k4_xboole_0(k2_xboole_0(X16,X17),k3_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t101_xboole_1])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X26,X27,X28,X29] : k3_enumset1(X26,X26,X27,X28,X29) = k2_enumset1(X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X19] : k5_xboole_0(X19,X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_29,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X30,X31,X32,X33,X34] : k4_enumset1(X30,X30,X31,X32,X33,X34) = k3_enumset1(X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_35,plain,(
    ! [X35,X36,X37,X38,X39,X40] : k5_enumset1(X35,X35,X36,X37,X38,X39,X40) = k4_enumset1(X35,X36,X37,X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_36,plain,(
    ! [X41] : k3_tarski(k1_tarski(X41)) = X41 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

fof(c_0_37,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_38,plain,(
    ! [X46] : k1_setfam_1(k1_tarski(X46)) = X46 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

fof(c_0_39,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_40,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( k5_xboole_0(X1,X2) = k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33])).

cnf(c_0_42,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43])).

cnf(c_0_49,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_24]),c_0_32]),c_0_33]),c_0_42]),c_0_43])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_45]),c_0_24]),c_0_32]),c_0_33]),c_0_42]),c_0_43])).

fof(c_0_51,plain,(
    ! [X68,X69] :
      ( ~ v1_relat_1(X68)
      | ~ v1_relat_1(X69)
      | k4_relat_1(k6_subset_1(X68,X69)) = k6_subset_1(k4_relat_1(X68),k4_relat_1(X69)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_relat_1])])])).

fof(c_0_52,plain,(
    ! [X44,X45] : k6_subset_1(X44,X45) = k4_xboole_0(X44,X45) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_54,plain,(
    ! [X57,X58,X59,X61,X62,X63,X64,X66] :
      ( ( ~ r2_hidden(X59,X58)
        | r2_hidden(k4_tarski(esk5_3(X57,X58,X59),X59),X57)
        | X58 != k2_relat_1(X57) )
      & ( ~ r2_hidden(k4_tarski(X62,X61),X57)
        | r2_hidden(X61,X58)
        | X58 != k2_relat_1(X57) )
      & ( ~ r2_hidden(esk6_2(X63,X64),X64)
        | ~ r2_hidden(k4_tarski(X66,esk6_2(X63,X64)),X63)
        | X64 = k2_relat_1(X63) )
      & ( r2_hidden(esk6_2(X63,X64),X64)
        | r2_hidden(k4_tarski(esk7_2(X63,X64),esk6_2(X63,X64)),X63)
        | X64 = k2_relat_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_57,plain,
    ( k4_relat_1(k6_subset_1(X1,X2)) = k6_subset_1(k4_relat_1(X1),k4_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X49,X50,X53,X55,X56] :
      ( ( ~ v1_relat_1(X49)
        | ~ r2_hidden(X50,X49)
        | X50 = k4_tarski(esk2_2(X49,X50),esk3_2(X49,X50)) )
      & ( r2_hidden(esk4_1(X53),X53)
        | v1_relat_1(X53) )
      & ( esk4_1(X53) != k4_tarski(X55,X56)
        | v1_relat_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_64,plain,
    ( k4_relat_1(k4_xboole_0(X1,X2)) = k4_xboole_0(k4_relat_1(X1),k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58]),c_0_58])).

cnf(c_0_65,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

fof(c_0_66,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t66_relat_1])).

cnf(c_0_67,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk6_2(X2,X1),X1)
    | ~ r2_hidden(k4_tarski(esk7_2(X2,X1),esk6_2(X2,X1)),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk7_2(k1_xboole_0,X1),esk6_2(k1_xboole_0,X1)),X2)
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_61]),c_0_63])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k4_relat_1(X1),k4_relat_1(X2)) = k4_relat_1(k4_xboole_0(X1,X2))
    | r2_hidden(esk4_1(X1),X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_70,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_66])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_63])])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k4_relat_1(X1),k4_relat_1(X2)) = k4_relat_1(k4_xboole_0(X1,X2))
    | r2_hidden(esk4_1(X2),X2)
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk6_2(k1_xboole_0,X1),k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_71])).

cnf(c_0_75,plain,
    ( r2_hidden(esk4_1(X1),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_72]),c_0_56]),c_0_56]),c_0_73])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(esk6_2(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_56])).

cnf(c_0_77,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,k4_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_71])).

cnf(c_0_78,plain,
    ( ~ r2_hidden(esk4_1(X1),k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_75])).

cnf(c_0_79,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,plain,
    ( ~ r2_hidden(esk4_1(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_81,plain,
    ( $false ),
    inference(spm,[status(thm)],[c_0_80,c_0_75]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:47:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.12/0.37  # and selection function SelectCQArNTNpEqFirst.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t93_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 0.12/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.37  fof(t101_xboole_1, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t101_xboole_1)).
% 0.12/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.37  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.12/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.37  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.12/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.37  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.12/0.37  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.12/0.37  fof(t41_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k6_subset_1(X1,X2))=k6_subset_1(k4_relat_1(X1),k4_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_relat_1)).
% 0.12/0.37  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.12/0.37  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.12/0.37  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.12/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.12/0.37  fof(t66_relat_1, conjecture, k4_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 0.12/0.37  fof(c_0_19, plain, ![X42, X43]:k3_tarski(k2_tarski(X42,X43))=k2_xboole_0(X42,X43), inference(variable_rename,[status(thm)],[t93_zfmisc_1])).
% 0.12/0.37  fof(c_0_20, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.37  fof(c_0_21, plain, ![X47, X48]:k1_setfam_1(k2_tarski(X47,X48))=k3_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.37  fof(c_0_22, plain, ![X16, X17]:k5_xboole_0(X16,X17)=k4_xboole_0(k2_xboole_0(X16,X17),k3_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t101_xboole_1])).
% 0.12/0.37  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_25, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.37  fof(c_0_26, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.37  fof(c_0_27, plain, ![X26, X27, X28, X29]:k3_enumset1(X26,X26,X27,X28,X29)=k2_enumset1(X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.37  fof(c_0_28, plain, ![X19]:k5_xboole_0(X19,X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.12/0.37  cnf(c_0_29, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.37  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_25, c_0_24])).
% 0.12/0.37  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  fof(c_0_34, plain, ![X30, X31, X32, X33, X34]:k4_enumset1(X30,X30,X31,X32,X33,X34)=k3_enumset1(X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.37  fof(c_0_35, plain, ![X35, X36, X37, X38, X39, X40]:k5_enumset1(X35,X35,X36,X37,X38,X39,X40)=k4_enumset1(X35,X36,X37,X38,X39,X40), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.37  fof(c_0_36, plain, ![X41]:k3_tarski(k1_tarski(X41))=X41, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.12/0.37  fof(c_0_37, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.37  fof(c_0_38, plain, ![X46]:k1_setfam_1(k1_tarski(X46))=X46, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.12/0.37  fof(c_0_39, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.12/0.37  cnf(c_0_40, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.37  cnf(c_0_41, plain, (k5_xboole_0(X1,X2)=k4_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33])).
% 0.12/0.37  cnf(c_0_42, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.37  cnf(c_0_43, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.37  cnf(c_0_44, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_45, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.37  cnf(c_0_46, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.37  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_48, plain, (k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43])).
% 0.12/0.37  cnf(c_0_49, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_24]), c_0_32]), c_0_33]), c_0_42]), c_0_43])).
% 0.12/0.37  cnf(c_0_50, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_45]), c_0_24]), c_0_32]), c_0_33]), c_0_42]), c_0_43])).
% 0.12/0.37  fof(c_0_51, plain, ![X68, X69]:(~v1_relat_1(X68)|(~v1_relat_1(X69)|k4_relat_1(k6_subset_1(X68,X69))=k6_subset_1(k4_relat_1(X68),k4_relat_1(X69)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_relat_1])])])).
% 0.12/0.37  fof(c_0_52, plain, ![X44, X45]:k6_subset_1(X44,X45)=k4_xboole_0(X44,X45), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.12/0.37  cnf(c_0_53, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  fof(c_0_54, plain, ![X57, X58, X59, X61, X62, X63, X64, X66]:(((~r2_hidden(X59,X58)|r2_hidden(k4_tarski(esk5_3(X57,X58,X59),X59),X57)|X58!=k2_relat_1(X57))&(~r2_hidden(k4_tarski(X62,X61),X57)|r2_hidden(X61,X58)|X58!=k2_relat_1(X57)))&((~r2_hidden(esk6_2(X63,X64),X64)|~r2_hidden(k4_tarski(X66,esk6_2(X63,X64)),X63)|X64=k2_relat_1(X63))&(r2_hidden(esk6_2(X63,X64),X64)|r2_hidden(k4_tarski(esk7_2(X63,X64),esk6_2(X63,X64)),X63)|X64=k2_relat_1(X63)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.12/0.37  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_47])).
% 0.12/0.37  cnf(c_0_56, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.12/0.37  cnf(c_0_57, plain, (k4_relat_1(k6_subset_1(X1,X2))=k6_subset_1(k4_relat_1(X1),k4_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.37  cnf(c_0_58, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.37  fof(c_0_59, plain, ![X49, X50, X53, X55, X56]:((~v1_relat_1(X49)|(~r2_hidden(X50,X49)|X50=k4_tarski(esk2_2(X49,X50),esk3_2(X49,X50))))&((r2_hidden(esk4_1(X53),X53)|v1_relat_1(X53))&(esk4_1(X53)!=k4_tarski(X55,X56)|v1_relat_1(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.12/0.37  cnf(c_0_60, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_53])).
% 0.12/0.37  cnf(c_0_61, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.12/0.37  cnf(c_0_62, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.12/0.37  cnf(c_0_63, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.37  cnf(c_0_64, plain, (k4_relat_1(k4_xboole_0(X1,X2))=k4_xboole_0(k4_relat_1(X1),k4_relat_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58]), c_0_58])).
% 0.12/0.37  cnf(c_0_65, plain, (r2_hidden(esk4_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.12/0.37  fof(c_0_66, negated_conjecture, ~(k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t66_relat_1])).
% 0.12/0.37  cnf(c_0_67, plain, (X1=k2_relat_1(X2)|r2_hidden(esk6_2(X2,X1),X1)|~r2_hidden(k4_tarski(esk7_2(X2,X1),esk6_2(X2,X1)),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.12/0.37  cnf(c_0_68, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk7_2(k1_xboole_0,X1),esk6_2(k1_xboole_0,X1)),X2)|r2_hidden(esk6_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_61]), c_0_63])).
% 0.12/0.37  cnf(c_0_69, plain, (k4_xboole_0(k4_relat_1(X1),k4_relat_1(X2))=k4_relat_1(k4_xboole_0(X1,X2))|r2_hidden(esk4_1(X1),X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.12/0.37  fof(c_0_70, negated_conjecture, k4_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_66])).
% 0.12/0.37  cnf(c_0_71, plain, (X1=k1_xboole_0|r2_hidden(esk6_2(k1_xboole_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_63])])).
% 0.12/0.37  cnf(c_0_72, plain, (k4_xboole_0(k4_relat_1(X1),k4_relat_1(X2))=k4_relat_1(k4_xboole_0(X1,X2))|r2_hidden(esk4_1(X2),X2)|r2_hidden(esk4_1(X1),X1)), inference(spm,[status(thm)],[c_0_69, c_0_65])).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.12/0.37  cnf(c_0_74, plain, (X1=k1_xboole_0|~r2_hidden(esk6_2(k1_xboole_0,X1),k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_60, c_0_71])).
% 0.12/0.37  cnf(c_0_75, plain, (r2_hidden(esk4_1(X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_72]), c_0_56]), c_0_56]), c_0_73])).
% 0.12/0.37  cnf(c_0_76, plain, (X1=k1_xboole_0|~r2_hidden(esk6_2(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_56])).
% 0.12/0.37  cnf(c_0_77, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk6_2(k1_xboole_0,k4_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_55, c_0_71])).
% 0.12/0.37  cnf(c_0_78, plain, (~r2_hidden(esk4_1(X1),k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_60, c_0_75])).
% 0.12/0.37  cnf(c_0_79, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.12/0.37  cnf(c_0_80, plain, (~r2_hidden(esk4_1(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.12/0.37  cnf(c_0_81, plain, ($false), inference(spm,[status(thm)],[c_0_80, c_0_75]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 82
% 0.12/0.37  # Proof object clause steps            : 44
% 0.12/0.37  # Proof object formula steps           : 38
% 0.12/0.37  # Proof object conjectures             : 4
% 0.12/0.37  # Proof object clause conjectures      : 1
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 20
% 0.12/0.37  # Proof object initial formulas used   : 19
% 0.12/0.37  # Proof object generating inferences   : 14
% 0.12/0.37  # Proof object simplifying inferences  : 37
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 21
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 32
% 0.12/0.37  # Removed in clause preprocessing      : 10
% 0.12/0.37  # Initial clauses in saturation        : 22
% 0.12/0.37  # Processed clauses                    : 97
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 21
% 0.12/0.37  # ...remaining for further processing  : 75
% 0.12/0.37  # Other redundant clauses eliminated   : 5
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 2
% 0.12/0.37  # Backward-rewritten                   : 3
% 0.12/0.37  # Generated clauses                    : 140
% 0.12/0.37  # ...of the previous two non-trivial   : 129
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 131
% 0.12/0.37  # Factorizations                       : 4
% 0.12/0.37  # Equation resolutions                 : 5
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 43
% 0.12/0.37  #    Positive orientable unit clauses  : 9
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 31
% 0.12/0.37  # Current number of unprocessed clauses: 75
% 0.12/0.37  # ...number of literals in the above   : 214
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 37
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 178
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 138
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 22
% 0.12/0.37  # Unit Clause-clause subsumption calls : 38
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 8
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3843
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.032 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.037 s
% 0.12/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
