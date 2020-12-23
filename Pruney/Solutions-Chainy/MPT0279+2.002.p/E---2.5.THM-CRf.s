%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:08 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  107 (1167 expanded)
%              Number of clauses        :   70 ( 532 expanded)
%              Number of leaves         :   18 ( 316 expanded)
%              Depth                    :   17
%              Number of atoms          :  179 (1670 expanded)
%              Number of equality atoms :  106 (1075 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t80_zfmisc_1,conjecture,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t91_enumset1,axiom,(
    ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t60_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => ( ( r2_hidden(X3,X2)
          & X1 != X3 )
        | k3_xboole_0(k2_tarski(X1,X3),X2) = k1_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(t78_enumset1,axiom,(
    ! [X1,X2,X3] : k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t40_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t49_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ( k4_xboole_0(X14,X15) != k1_xboole_0
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | k4_xboole_0(X14,X15) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X23,X24] : r1_xboole_0(k4_xboole_0(X23,X24),X24) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)) ),
    inference(assume_negation,[status(cth)],[t80_zfmisc_1])).

fof(c_0_25,plain,(
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

fof(c_0_26,plain,(
    ! [X51,X52] : k3_tarski(k2_tarski(X51,X52)) = k2_xboole_0(X51,X52) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_27,plain,(
    ! [X27,X28] : k1_enumset1(X27,X27,X28) = k2_tarski(X27,X28) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_31,negated_conjecture,(
    ~ r1_tarski(k1_tarski(esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_32,plain,(
    ! [X43] : k4_enumset1(X43,X43,X43,X43,X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t91_enumset1])).

fof(c_0_33,plain,(
    ! [X34,X35,X36,X37,X38,X39] : k5_enumset1(X34,X34,X35,X36,X37,X38,X39) = k4_enumset1(X34,X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_34,plain,(
    ! [X53,X54,X55] :
      ( ( r2_hidden(X55,X54)
        | k3_xboole_0(k2_tarski(X53,X55),X54) = k1_tarski(X53)
        | ~ r2_hidden(X53,X54) )
      & ( X53 != X55
        | k3_xboole_0(k2_tarski(X53,X55),X54) = k1_tarski(X53)
        | ~ r2_hidden(X53,X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).

fof(c_0_35,plain,(
    ! [X40,X41,X42] : k3_enumset1(X40,X40,X40,X41,X42) = k1_enumset1(X40,X41,X42) ),
    inference(variable_rename,[status(thm)],[t78_enumset1])).

fof(c_0_36,plain,(
    ! [X29,X30,X31,X32,X33] : k4_enumset1(X29,X29,X30,X31,X32,X33) = k3_enumset1(X29,X30,X31,X32,X33) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_38,plain,(
    ! [X16,X17] : k4_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X16,X17) ),
    inference(variable_rename,[status(thm)],[t40_xboole_1])).

cnf(c_0_39,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_41,plain,(
    ! [X21,X22] : k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22)) = X21 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

fof(c_0_42,plain,(
    ! [X25,X26] :
      ( ( ~ r1_xboole_0(X25,X26)
        | k4_xboole_0(X25,X26) = X25 )
      & ( k4_xboole_0(X25,X26) != X25
        | r1_xboole_0(X25,X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_44,plain,(
    ! [X7,X8] :
      ( ( ~ r1_xboole_0(X7,X8)
        | k3_xboole_0(X7,X8) = k1_xboole_0 )
      & ( k3_xboole_0(X7,X8) != k1_xboole_0
        | r1_xboole_0(X7,X8) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( k4_enumset1(X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X2)
    | k3_xboole_0(k2_tarski(X3,X1),X2) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( k3_enumset1(X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_54,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_55,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_56,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_57,plain,(
    ! [X18,X19,X20] : k3_xboole_0(X18,k4_xboole_0(X19,X20)) = k4_xboole_0(k3_xboole_0(X18,X19),X20) ),
    inference(variable_rename,[status(thm)],[t49_xboole_1])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_29])).

cnf(c_0_60,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2) = k5_enumset1(X3,X3,X3,X3,X3,X3,X3)
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_40]),c_0_47]),c_0_51]),c_0_52]),c_0_48]),c_0_48])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_23])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),X2) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_51]),c_0_52]),c_0_48])).

cnf(c_0_67,plain,
    ( k3_tarski(k5_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_55]),c_0_51]),c_0_52]),c_0_48])).

cnf(c_0_68,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_70,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k1_zfmisc_1(X1)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,X2)) = k3_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),X2) = k4_xboole_0(X2,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_30]),c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( k3_xboole_0(k5_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) = k5_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | k4_xboole_0(X1,X2) != X1 ),
    inference(spm,[status(thm)],[c_0_60,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(k5_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_30])).

cnf(c_0_81,plain,
    ( k3_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_78]),c_0_78])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k1_xboole_0
    | k4_xboole_0(X1,X2) != X1 ),
    inference(rw,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_84,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_45])).

cnf(c_0_85,plain,
    ( k3_tarski(k5_enumset1(k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(X1,k4_xboole_0(X2,X3)))) = X1 ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(X1,k5_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k1_zfmisc_1(esk2_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_80]),c_0_70])).

cnf(c_0_87,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_61])).

cnf(c_0_88,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),X3) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | X1 != X2
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_40]),c_0_47]),c_0_51]),c_0_52]),c_0_48]),c_0_48])).

cnf(c_0_89,plain,
    ( k3_tarski(k5_enumset1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_78]),c_0_78]),c_0_78]),c_0_78]),c_0_78]),c_0_78])).

cnf(c_0_90,plain,
    ( k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))
    | k4_xboole_0(X1,X2) != X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_80]),c_0_87])).

cnf(c_0_92,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = X1
    | k4_xboole_0(X1,X2) != X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

cnf(c_0_94,plain,
    ( k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1)) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_65])).

cnf(c_0_95,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_30]),c_0_87])).

cnf(c_0_96,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,X2)
    | k4_xboole_0(X3,X1) != X3 ),
    inference(spm,[status(thm)],[c_0_69,c_0_93])).

cnf(c_0_97,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X2) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_29])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1))) = k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[c_0_94,c_0_78])).

cnf(c_0_99,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != X1 ),
    inference(spm,[status(thm)],[c_0_83,c_0_95])).

cnf(c_0_100,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1)) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_102,plain,
    ( k4_xboole_0(k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1)),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_98])).

cnf(c_0_103,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_zfmisc_1(esk2_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_101])).

cnf(c_0_105,plain,
    ( k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_105])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:44:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.48/0.65  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.48/0.65  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.48/0.65  #
% 0.48/0.65  # Preprocessing time       : 0.028 s
% 0.48/0.65  # Presaturation interreduction done
% 0.48/0.65  
% 0.48/0.65  # Proof found!
% 0.48/0.65  # SZS status Theorem
% 0.48/0.65  # SZS output start CNFRefutation
% 0.48/0.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.48/0.65  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.48/0.65  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.48/0.65  fof(t80_zfmisc_1, conjecture, ![X1]:r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 0.48/0.65  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.48/0.65  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.48/0.65  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.65  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.48/0.65  fof(t91_enumset1, axiom, ![X1]:k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_enumset1)).
% 0.48/0.65  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.48/0.65  fof(t60_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>((r2_hidden(X3,X2)&X1!=X3)|k3_xboole_0(k2_tarski(X1,X3),X2)=k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 0.48/0.65  fof(t78_enumset1, axiom, ![X1, X2, X3]:k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 0.48/0.65  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.48/0.65  fof(t40_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 0.48/0.65  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 0.48/0.65  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.48/0.65  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.48/0.65  fof(t49_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 0.48/0.65  fof(c_0_18, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.48/0.65  fof(c_0_19, plain, ![X14, X15]:((k4_xboole_0(X14,X15)!=k1_xboole_0|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|k4_xboole_0(X14,X15)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.48/0.65  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.48/0.65  fof(c_0_21, plain, ![X23, X24]:r1_xboole_0(k4_xboole_0(X23,X24),X24), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.48/0.65  cnf(c_0_22, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.65  cnf(c_0_23, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 0.48/0.65  fof(c_0_24, negated_conjecture, ~(![X1]:r1_tarski(k1_tarski(X1),k1_zfmisc_1(X1))), inference(assume_negation,[status(cth)],[t80_zfmisc_1])).
% 0.48/0.65  fof(c_0_25, plain, ![X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X46,X45)|r1_tarski(X46,X44)|X45!=k1_zfmisc_1(X44))&(~r1_tarski(X47,X44)|r2_hidden(X47,X45)|X45!=k1_zfmisc_1(X44)))&((~r2_hidden(esk1_2(X48,X49),X49)|~r1_tarski(esk1_2(X48,X49),X48)|X49=k1_zfmisc_1(X48))&(r2_hidden(esk1_2(X48,X49),X49)|r1_tarski(esk1_2(X48,X49),X48)|X49=k1_zfmisc_1(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.48/0.65  fof(c_0_26, plain, ![X51, X52]:k3_tarski(k2_tarski(X51,X52))=k2_xboole_0(X51,X52), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.48/0.65  fof(c_0_27, plain, ![X27, X28]:k1_enumset1(X27,X27,X28)=k2_tarski(X27,X28), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.65  fof(c_0_28, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.48/0.65  cnf(c_0_29, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.48/0.65  cnf(c_0_30, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.48/0.65  fof(c_0_31, negated_conjecture, ~r1_tarski(k1_tarski(esk2_0),k1_zfmisc_1(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.48/0.65  fof(c_0_32, plain, ![X43]:k4_enumset1(X43,X43,X43,X43,X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t91_enumset1])).
% 0.48/0.65  fof(c_0_33, plain, ![X34, X35, X36, X37, X38, X39]:k5_enumset1(X34,X34,X35,X36,X37,X38,X39)=k4_enumset1(X34,X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.48/0.65  fof(c_0_34, plain, ![X53, X54, X55]:((r2_hidden(X55,X54)|k3_xboole_0(k2_tarski(X53,X55),X54)=k1_tarski(X53)|~r2_hidden(X53,X54))&(X53!=X55|k3_xboole_0(k2_tarski(X53,X55),X54)=k1_tarski(X53)|~r2_hidden(X53,X54))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_zfmisc_1])])])).
% 0.48/0.65  fof(c_0_35, plain, ![X40, X41, X42]:k3_enumset1(X40,X40,X40,X41,X42)=k1_enumset1(X40,X41,X42), inference(variable_rename,[status(thm)],[t78_enumset1])).
% 0.48/0.65  fof(c_0_36, plain, ![X29, X30, X31, X32, X33]:k4_enumset1(X29,X29,X30,X31,X32,X33)=k3_enumset1(X29,X30,X31,X32,X33), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.48/0.65  cnf(c_0_37, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.65  fof(c_0_38, plain, ![X16, X17]:k4_xboole_0(k2_xboole_0(X16,X17),X17)=k4_xboole_0(X16,X17), inference(variable_rename,[status(thm)],[t40_xboole_1])).
% 0.48/0.65  cnf(c_0_39, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.48/0.65  cnf(c_0_40, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.48/0.65  fof(c_0_41, plain, ![X21, X22]:k2_xboole_0(k3_xboole_0(X21,X22),k4_xboole_0(X21,X22))=X21, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 0.48/0.65  fof(c_0_42, plain, ![X25, X26]:((~r1_xboole_0(X25,X26)|k4_xboole_0(X25,X26)=X25)&(k4_xboole_0(X25,X26)!=X25|r1_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.48/0.65  cnf(c_0_43, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.48/0.65  fof(c_0_44, plain, ![X7, X8]:((~r1_xboole_0(X7,X8)|k3_xboole_0(X7,X8)=k1_xboole_0)&(k3_xboole_0(X7,X8)!=k1_xboole_0|r1_xboole_0(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.48/0.65  cnf(c_0_45, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.48/0.65  cnf(c_0_46, negated_conjecture, (~r1_tarski(k1_tarski(esk2_0),k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.48/0.65  cnf(c_0_47, plain, (k4_enumset1(X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.48/0.65  cnf(c_0_48, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.48/0.65  cnf(c_0_49, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.65  cnf(c_0_50, plain, (r2_hidden(X1,X2)|k3_xboole_0(k2_tarski(X3,X1),X2)=k1_tarski(X3)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.48/0.65  cnf(c_0_51, plain, (k3_enumset1(X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.48/0.65  cnf(c_0_52, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.48/0.65  cnf(c_0_53, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_37])).
% 0.48/0.65  cnf(c_0_54, plain, (k4_xboole_0(k2_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.48/0.65  cnf(c_0_55, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.48/0.65  cnf(c_0_56, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.48/0.65  fof(c_0_57, plain, ![X18, X19, X20]:k3_xboole_0(X18,k4_xboole_0(X19,X20))=k4_xboole_0(k3_xboole_0(X18,X19),X20), inference(variable_rename,[status(thm)],[t49_xboole_1])).
% 0.48/0.65  cnf(c_0_58, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.48/0.65  cnf(c_0_59, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_43, c_0_29])).
% 0.48/0.65  cnf(c_0_60, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.48/0.65  cnf(c_0_61, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_45])).
% 0.48/0.65  cnf(c_0_62, negated_conjecture, (~r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_zfmisc_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.48/0.65  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_49])).
% 0.48/0.65  cnf(c_0_64, plain, (k3_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X1),X2)=k5_enumset1(X3,X3,X3,X3,X3,X3,X3)|r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_40]), c_0_47]), c_0_51]), c_0_52]), c_0_48]), c_0_48])).
% 0.48/0.65  cnf(c_0_65, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_53, c_0_23])).
% 0.48/0.65  cnf(c_0_66, plain, (k4_xboole_0(k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)),X2)=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_51]), c_0_52]), c_0_48])).
% 0.48/0.65  cnf(c_0_67, plain, (k3_tarski(k5_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_55]), c_0_51]), c_0_52]), c_0_48])).
% 0.48/0.65  cnf(c_0_68, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.48/0.65  cnf(c_0_69, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=X1), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.48/0.65  cnf(c_0_70, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.48/0.65  cnf(c_0_71, negated_conjecture, (~r2_hidden(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.48/0.65  cnf(c_0_72, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k1_zfmisc_1(X1))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X2,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.48/0.65  cnf(c_0_73, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.48/0.65  cnf(c_0_74, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,X2))=k3_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.48/0.65  cnf(c_0_75, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.48/0.65  cnf(c_0_76, plain, (k4_xboole_0(k3_xboole_0(X1,X2),X2)=k4_xboole_0(X2,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_30]), c_0_68])).
% 0.48/0.65  cnf(c_0_77, negated_conjecture, (k3_xboole_0(k5_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))=k5_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.48/0.65  cnf(c_0_78, plain, (k3_xboole_0(X1,X2)=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.48/0.65  cnf(c_0_79, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|k4_xboole_0(X1,X2)!=X1), inference(spm,[status(thm)],[c_0_60, c_0_75])).
% 0.48/0.65  cnf(c_0_80, negated_conjecture, (k4_xboole_0(k5_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0)),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_30])).
% 0.48/0.65  cnf(c_0_81, plain, (k3_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.48/0.65  cnf(c_0_82, plain, (k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X3)=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_78]), c_0_78])).
% 0.48/0.65  cnf(c_0_83, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k1_xboole_0|k4_xboole_0(X1,X2)!=X1), inference(rw,[status(thm)],[c_0_79, c_0_78])).
% 0.48/0.65  cnf(c_0_84, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_45])).
% 0.48/0.65  cnf(c_0_85, plain, (k3_tarski(k5_enumset1(k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(k3_xboole_0(X1,X2),X3),k4_xboole_0(X1,k4_xboole_0(X2,X3))))=X1), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.48/0.65  cnf(c_0_86, negated_conjecture, (k4_xboole_0(k3_xboole_0(X1,k5_enumset1(k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0),k1_zfmisc_1(esk2_0))),k1_zfmisc_1(k1_zfmisc_1(esk2_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_80]), c_0_70])).
% 0.48/0.65  cnf(c_0_87, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_58, c_0_61])).
% 0.48/0.65  cnf(c_0_88, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),X3)=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|X1!=X2|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_40]), c_0_47]), c_0_51]), c_0_52]), c_0_48]), c_0_48])).
% 0.48/0.65  cnf(c_0_89, plain, (k3_tarski(k5_enumset1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_78]), c_0_78]), c_0_78]), c_0_78]), c_0_78]), c_0_78])).
% 0.48/0.65  cnf(c_0_90, plain, (k1_xboole_0=k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X3)))|k4_xboole_0(X1,X2)!=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])).
% 0.48/0.65  cnf(c_0_91, negated_conjecture, (k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_80]), c_0_87])).
% 0.48/0.65  cnf(c_0_92, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_88])).
% 0.48/0.65  cnf(c_0_93, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=X1|k4_xboole_0(X1,X2)!=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91])).
% 0.48/0.65  cnf(c_0_94, plain, (k3_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(spm,[status(thm)],[c_0_92, c_0_65])).
% 0.48/0.65  cnf(c_0_95, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X2)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_30]), c_0_87])).
% 0.48/0.65  cnf(c_0_96, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,X2)|k4_xboole_0(X3,X1)!=X3), inference(spm,[status(thm)],[c_0_69, c_0_93])).
% 0.48/0.65  cnf(c_0_97, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X2)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_58, c_0_29])).
% 0.48/0.65  cnf(c_0_98, plain, (k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1)))=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[c_0_94, c_0_78])).
% 0.48/0.65  cnf(c_0_99, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=X1), inference(spm,[status(thm)],[c_0_83, c_0_95])).
% 0.48/0.65  cnf(c_0_100, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X3,X1))=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.48/0.65  cnf(c_0_101, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.65  cnf(c_0_102, plain, (k4_xboole_0(k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1)),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_98])).
% 0.48/0.65  cnf(c_0_103, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.48/0.65  cnf(c_0_104, negated_conjecture, (k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k1_zfmisc_1(esk2_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_101])).
% 0.48/0.65  cnf(c_0_105, plain, (k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_zfmisc_1(X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 0.48/0.65  cnf(c_0_106, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_105])]), ['proof']).
% 0.48/0.65  # SZS output end CNFRefutation
% 0.48/0.65  # Proof object total steps             : 107
% 0.48/0.65  # Proof object clause steps            : 70
% 0.48/0.65  # Proof object formula steps           : 37
% 0.48/0.65  # Proof object conjectures             : 12
% 0.48/0.65  # Proof object clause conjectures      : 9
% 0.48/0.65  # Proof object formula conjectures     : 3
% 0.48/0.65  # Proof object initial clauses used    : 22
% 0.48/0.65  # Proof object initial formulas used   : 18
% 0.48/0.65  # Proof object generating inferences   : 31
% 0.48/0.65  # Proof object simplifying inferences  : 49
% 0.48/0.65  # Training examples: 0 positive, 0 negative
% 0.48/0.65  # Parsed axioms                        : 19
% 0.48/0.65  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.65  # Initial clauses                      : 28
% 0.48/0.65  # Removed in clause preprocessing      : 6
% 0.48/0.65  # Initial clauses in saturation        : 22
% 0.48/0.65  # Processed clauses                    : 2483
% 0.48/0.65  # ...of these trivial                  : 119
% 0.48/0.65  # ...subsumed                          : 2006
% 0.48/0.65  # ...remaining for further processing  : 358
% 0.48/0.65  # Other redundant clauses eliminated   : 1719
% 0.48/0.65  # Clauses deleted for lack of memory   : 0
% 0.48/0.65  # Backward-subsumed                    : 9
% 0.48/0.65  # Backward-rewritten                   : 74
% 0.48/0.65  # Generated clauses                    : 32992
% 0.48/0.65  # ...of the previous two non-trivial   : 20911
% 0.48/0.65  # Contextual simplify-reflections      : 0
% 0.48/0.65  # Paramodulations                      : 31260
% 0.48/0.65  # Factorizations                       : 4
% 0.48/0.65  # Equation resolutions                 : 1728
% 0.48/0.65  # Propositional unsat checks           : 0
% 0.48/0.65  #    Propositional check models        : 0
% 0.48/0.65  #    Propositional check unsatisfiable : 0
% 0.48/0.65  #    Propositional clauses             : 0
% 0.48/0.65  #    Propositional clauses after purity: 0
% 0.48/0.65  #    Propositional unsat core size     : 0
% 0.48/0.65  #    Propositional preprocessing time  : 0.000
% 0.48/0.65  #    Propositional encoding time       : 0.000
% 0.48/0.65  #    Propositional solver time         : 0.000
% 0.48/0.65  #    Success case prop preproc time    : 0.000
% 0.48/0.65  #    Success case prop encoding time   : 0.000
% 0.48/0.65  #    Success case prop solver time     : 0.000
% 0.48/0.65  # Current number of processed clauses  : 249
% 0.48/0.65  #    Positive orientable unit clauses  : 54
% 0.48/0.65  #    Positive unorientable unit clauses: 5
% 0.48/0.65  #    Negative unit clauses             : 2
% 0.48/0.65  #    Non-unit-clauses                  : 188
% 0.48/0.65  # Current number of unprocessed clauses: 17290
% 0.48/0.65  # ...number of literals in the above   : 42926
% 0.48/0.65  # Current number of archived formulas  : 0
% 0.48/0.65  # Current number of archived clauses   : 110
% 0.48/0.65  # Clause-clause subsumption calls (NU) : 15349
% 0.48/0.65  # Rec. Clause-clause subsumption calls : 13942
% 0.48/0.65  # Non-unit clause-clause subsumptions  : 1087
% 0.48/0.65  # Unit Clause-clause subsumption calls : 161
% 0.48/0.65  # Rewrite failures with RHS unbound    : 125
% 0.48/0.65  # BW rewrite match attempts            : 768
% 0.48/0.65  # BW rewrite match successes           : 73
% 0.48/0.65  # Condensation attempts                : 0
% 0.48/0.65  # Condensation successes               : 0
% 0.48/0.65  # Termbank termtop insertions          : 910831
% 0.48/0.65  
% 0.48/0.65  # -------------------------------------------------
% 0.48/0.65  # User time                : 0.304 s
% 0.48/0.65  # System time              : 0.014 s
% 0.48/0.65  # Total time               : 0.318 s
% 0.48/0.65  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
