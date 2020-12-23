%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:38:19 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  162 (110400 expanded)
%              Number of clauses        :  113 (49753 expanded)
%              Number of leaves         :   24 (29993 expanded)
%              Depth                    :   45
%              Number of atoms          :  252 (135689 expanded)
%              Number of equality atoms :  177 (109381 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t21_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_xboole_0
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(t64_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_enumset1)).

fof(t89_enumset1,axiom,(
    ! [X1,X2,X3] : k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

fof(t80_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(t96_enumset1,axiom,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).

fof(l68_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t109_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k4_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t99_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(t5_xboole_1,axiom,(
    ! [X1,X2,X3] : k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(t55_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t57_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(t83_enumset1,axiom,(
    ! [X1,X2] : k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t47_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(l75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_xboole_0
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t21_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X72,X73,X74,X75,X76,X77,X78,X79] : k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79) = k2_xboole_0(k1_enumset1(X72,X73,X74),k3_enumset1(X75,X76,X77,X78,X79)) ),
    inference(variable_rename,[status(thm)],[t64_enumset1])).

fof(c_0_26,plain,(
    ! [X91,X92,X93] : k5_enumset1(X91,X91,X91,X91,X91,X92,X93) = k1_enumset1(X91,X92,X93) ),
    inference(variable_rename,[status(thm)],[t89_enumset1])).

fof(c_0_27,plain,(
    ! [X84,X85,X86,X87,X88] : k5_enumset1(X84,X84,X84,X85,X86,X87,X88) = k3_enumset1(X84,X85,X86,X87,X88) ),
    inference(variable_rename,[status(thm)],[t80_enumset1])).

fof(c_0_28,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_xboole_0
    & esk2_0 != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_29,plain,(
    ! [X94] : k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X94) = k1_tarski(X94) ),
    inference(variable_rename,[status(thm)],[t96_enumset1])).

cnf(c_0_30,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] : k5_enumset1(X45,X46,X47,X48,X49,X50,X51) = k2_xboole_0(k2_enumset1(X45,X46,X47,X48),k1_enumset1(X49,X50,X51)) ),
    inference(variable_rename,[status(thm)],[l68_enumset1])).

fof(c_0_34,plain,(
    ! [X80,X81,X82,X83] : k3_enumset1(X80,X80,X81,X82,X83) = k2_enumset1(X80,X81,X82,X83) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_35,negated_conjecture,
    ( k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X11,X12,X13] :
      ( ~ r1_tarski(X11,X12)
      | r1_tarski(k4_xboole_0(X11,X13),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k2_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_42,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X6,X7)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39]),c_0_31]),c_0_32])).

cnf(c_0_43,plain,
    ( r1_tarski(k4_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

fof(c_0_45,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_48,plain,(
    ! [X22,X23] : k4_xboole_0(X22,k2_xboole_0(X22,X23)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1)
    | k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_51,plain,(
    ! [X24,X25,X26] : k4_xboole_0(X24,k4_xboole_0(X25,X26)) = k2_xboole_0(k4_xboole_0(X24,X25),k3_xboole_0(X24,X26)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_44])).

cnf(c_0_54,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_50])).

cnf(c_0_55,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | k4_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_47])).

fof(c_0_58,plain,(
    ! [X33,X34,X35] : k4_xboole_0(k5_xboole_0(X33,X34),X35) = k2_xboole_0(k4_xboole_0(X33,k2_xboole_0(X34,X35)),k4_xboole_0(X34,k2_xboole_0(X33,X35))) ),
    inference(variable_rename,[status(thm)],[t99_xboole_1])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_50])).

cnf(c_0_61,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X2),X3) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1))) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_50])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_60])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X1),X2) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_50]),c_0_50])).

cnf(c_0_65,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_62])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X2,X3))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_55])).

cnf(c_0_67,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_64])).

fof(c_0_68,plain,(
    ! [X29] : k5_xboole_0(X29,k1_xboole_0) = X29 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_69,plain,(
    ! [X30,X31,X32] : k2_xboole_0(k2_xboole_0(X30,X31),X32) = k2_xboole_0(k2_xboole_0(X30,X32),k2_xboole_0(X31,X32)) ),
    inference(variable_rename,[status(thm)],[t5_xboole_1])).

cnf(c_0_70,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X1)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_65])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_66])).

cnf(c_0_72,plain,
    ( k4_xboole_0(k5_xboole_0(X1,X1),X2) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_67])).

cnf(c_0_73,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( k2_xboole_0(k2_xboole_0(X1,X2),X3) = k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

fof(c_0_77,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | r1_tarski(X14,k2_xboole_0(X16,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

cnf(c_0_78,plain,
    ( k2_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(X1,k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_83,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X1,X3),X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_74])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_47])).

fof(c_0_85,plain,(
    ! [X17,X18] :
      ( k4_xboole_0(X17,X18) != k4_xboole_0(X18,X17)
      | X17 = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_86,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_50])).

cnf(c_0_88,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_86]),c_0_73]),c_0_76]),c_0_67])).

fof(c_0_90,plain,(
    ! [X27,X28] : k4_xboole_0(k2_xboole_0(X27,X28),k3_xboole_0(X27,X28)) = k2_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X28,X27)) ),
    inference(variable_rename,[status(thm)],[t55_xboole_1])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) = X1
    | k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_93,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X2,X3)) = k1_xboole_0
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_52,c_0_80])).

cnf(c_0_94,plain,
    ( k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_91]),c_0_76])])).

cnf(c_0_96,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_97,plain,
    ( k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_67]),c_0_73]),c_0_63])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_67]),c_0_63])).

cnf(c_0_99,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_76])).

cnf(c_0_100,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) = X1
    | k4_xboole_0(X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_47])).

cnf(c_0_101,plain,
    ( k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_97])).

cnf(c_0_102,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_99])).

cnf(c_0_104,plain,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_105,plain,
    ( r1_tarski(k4_xboole_0(X1,k1_xboole_0),X2)
    | ~ r1_tarski(k5_xboole_0(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_104])).

fof(c_0_106,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(k4_xboole_0(X19,X20),X21)
      | r1_tarski(X19,k2_xboole_0(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_107,plain,
    ( r1_tarski(k4_xboole_0(X1,k1_xboole_0),X2)
    | k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_47])).

cnf(c_0_108,negated_conjecture,
    ( k4_xboole_0(k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)),X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_86]),c_0_76]),c_0_67])).

cnf(c_0_109,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k4_xboole_0(X1,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_103])).

cnf(c_0_111,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_112,negated_conjecture,
    ( k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_111])).

cnf(c_0_113,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | k4_xboole_0(k4_xboole_0(X1,X2),X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_109,c_0_47])).

cnf(c_0_114,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_112])])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_116,negated_conjecture,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_112,c_0_114])).

cnf(c_0_117,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_110])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

fof(c_0_119,plain,(
    ! [X95,X96] :
      ( ( ~ r1_tarski(X95,k1_tarski(X96))
        | X95 = k1_xboole_0
        | X95 = k1_tarski(X96) )
      & ( X95 != k1_xboole_0
        | r1_tarski(X95,k1_tarski(X96)) )
      & ( X95 != k1_tarski(X96)
        | r1_tarski(X95,k1_tarski(X96)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_120,plain,(
    ! [X65,X66,X67,X68,X69,X70,X71] : k5_enumset1(X65,X66,X67,X68,X69,X70,X71) = k2_xboole_0(k2_tarski(X65,X66),k3_enumset1(X67,X68,X69,X70,X71)) ),
    inference(variable_rename,[status(thm)],[t57_enumset1])).

fof(c_0_121,plain,(
    ! [X89,X90] : k3_enumset1(X89,X89,X89,X89,X90) = k2_tarski(X89,X90) ),
    inference(variable_rename,[status(thm)],[t83_enumset1])).

cnf(c_0_122,negated_conjecture,
    ( k4_xboole_0(X1,k1_xboole_0) = X1
    | k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_117])).

cnf(c_0_123,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_118])).

fof(c_0_124,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X39,X38)
        | X39 = X36
        | X39 = X37
        | X38 != k2_tarski(X36,X37) )
      & ( X40 != X36
        | r2_hidden(X40,X38)
        | X38 != k2_tarski(X36,X37) )
      & ( X40 != X37
        | r2_hidden(X40,X38)
        | X38 != k2_tarski(X36,X37) )
      & ( esk1_3(X41,X42,X43) != X41
        | ~ r2_hidden(esk1_3(X41,X42,X43),X43)
        | X43 = k2_tarski(X41,X42) )
      & ( esk1_3(X41,X42,X43) != X42
        | ~ r2_hidden(esk1_3(X41,X42,X43),X43)
        | X43 = k2_tarski(X41,X42) )
      & ( r2_hidden(esk1_3(X41,X42,X43),X43)
        | esk1_3(X41,X42,X43) = X41
        | esk1_3(X41,X42,X43) = X42
        | X43 = k2_tarski(X41,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_125,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_126,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_127,plain,
    ( k3_enumset1(X1,X1,X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_128,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_72])).

cnf(c_0_129,negated_conjecture,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_123])])).

cnf(c_0_130,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_131,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))
    | ~ r1_tarski(X1,k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_132,plain,
    ( k5_enumset1(X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X4,X5,X6,X7)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126,c_0_127]),c_0_32]),c_0_32])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_44]),c_0_128])])).

cnf(c_0_134,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_129]),c_0_129])).

cnf(c_0_135,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_136,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X2,X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_127]),c_0_32])).

cnf(c_0_137,plain,
    ( X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131,c_0_132]),c_0_132])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_139,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_127]),c_0_32])).

cnf(c_0_140,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_136])])).

cnf(c_0_141,negated_conjecture,
    ( k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) = k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)
    | k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_142,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k5_enumset1(X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_139])).

cnf(c_0_143,negated_conjecture,
    ( k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0
    | r2_hidden(esk3_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_144,negated_conjecture,
    ( esk2_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_145,plain,(
    ! [X60,X61,X62,X63,X64] : k3_enumset1(X60,X61,X62,X63,X64) = k2_xboole_0(k1_tarski(X60),k2_enumset1(X61,X62,X63,X64)) ),
    inference(variable_rename,[status(thm)],[t47_enumset1])).

fof(c_0_146,plain,(
    ! [X52,X53,X54,X55,X56,X57,X58,X59] : k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59) = k2_xboole_0(k2_enumset1(X52,X53,X54,X55),k2_enumset1(X56,X57,X58,X59)) ),
    inference(variable_rename,[status(thm)],[l75_enumset1])).

cnf(c_0_147,negated_conjecture,
    ( k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_144])).

cnf(c_0_148,plain,
    ( k3_enumset1(X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(split_conjunct,[status(thm)],[c_0_145])).

cnf(c_0_149,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k5_enumset1(X1,X2,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_147]),c_0_134])).

cnf(c_0_151,plain,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k5_enumset1(X2,X2,X2,X2,X3,X4,X5)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148,c_0_39]),c_0_36]),c_0_32]),c_0_32]),c_0_37])).

cnf(c_0_152,plain,
    ( k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8)) = k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X6,X7,X8)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_39]),c_0_39]),c_0_32]),c_0_32]),c_0_37])).

cnf(c_0_153,negated_conjecture,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k5_enumset1(X3,X2,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_150])).

cnf(c_0_154,plain,
    ( k5_enumset1(X1,X1,X2,X2,X3,X4,X5) = k5_enumset1(X1,X1,X1,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_151,c_0_42]),c_0_132])).

cnf(c_0_155,negated_conjecture,
    ( k5_enumset1(X1,X1,X1,X2,X3,X4,X5) = k5_enumset1(esk2_0,X1,X2,X2,X3,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152,c_0_147]),c_0_114]),c_0_132])).

cnf(c_0_156,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(X2,X2,X2,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_153,c_0_154])).

cnf(c_0_157,negated_conjecture,
    ( r2_hidden(X1,k5_enumset1(esk2_0,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_155])).

cnf(c_0_158,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(X1,k5_enumset1(esk2_0,X2,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_156,c_0_155])).

cnf(c_0_159,negated_conjecture,
    ( r2_hidden(esk2_0,k5_enumset1(esk2_0,X1,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_157,c_0_150])).

cnf(c_0_160,negated_conjecture,
    ( esk2_0 = X1 ),
    inference(spm,[status(thm)],[c_0_158,c_0_159])).

cnf(c_0_161,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_160])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:49:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.40  #
% 0.18/0.40  # Preprocessing time       : 0.028 s
% 0.18/0.40  # Presaturation interreduction done
% 0.18/0.40  
% 0.18/0.40  # Proof found!
% 0.18/0.40  # SZS status Theorem
% 0.18/0.40  # SZS output start CNFRefutation
% 0.18/0.40  fof(t21_zfmisc_1, conjecture, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_xboole_0=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 0.18/0.40  fof(t64_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_enumset1)).
% 0.18/0.40  fof(t89_enumset1, axiom, ![X1, X2, X3]:k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_enumset1)).
% 0.18/0.40  fof(t80_enumset1, axiom, ![X1, X2, X3, X4, X5]:k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_enumset1)).
% 0.18/0.40  fof(t96_enumset1, axiom, ![X1]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_enumset1)).
% 0.18/0.40  fof(l68_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_enumset1)).
% 0.18/0.40  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.40  fof(t109_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(k4_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 0.18/0.40  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.18/0.40  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.18/0.40  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.18/0.40  fof(t99_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_xboole_1)).
% 0.18/0.40  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.18/0.40  fof(t5_xboole_1, axiom, ![X1, X2, X3]:k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_1)).
% 0.18/0.40  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 0.18/0.40  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.18/0.40  fof(t55_xboole_1, axiom, ![X1, X2]:k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_xboole_1)).
% 0.18/0.40  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 0.18/0.40  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.18/0.40  fof(t57_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_enumset1)).
% 0.18/0.40  fof(t83_enumset1, axiom, ![X1, X2]:k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 0.18/0.40  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.18/0.40  fof(t47_enumset1, axiom, ![X1, X2, X3, X4, X5]:k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_enumset1)).
% 0.18/0.40  fof(l75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l75_enumset1)).
% 0.18/0.40  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_xboole_0=>X1=X2)), inference(assume_negation,[status(cth)],[t21_zfmisc_1])).
% 0.18/0.40  fof(c_0_25, plain, ![X72, X73, X74, X75, X76, X77, X78, X79]:k6_enumset1(X72,X73,X74,X75,X76,X77,X78,X79)=k2_xboole_0(k1_enumset1(X72,X73,X74),k3_enumset1(X75,X76,X77,X78,X79)), inference(variable_rename,[status(thm)],[t64_enumset1])).
% 0.18/0.40  fof(c_0_26, plain, ![X91, X92, X93]:k5_enumset1(X91,X91,X91,X91,X91,X92,X93)=k1_enumset1(X91,X92,X93), inference(variable_rename,[status(thm)],[t89_enumset1])).
% 0.18/0.40  fof(c_0_27, plain, ![X84, X85, X86, X87, X88]:k5_enumset1(X84,X84,X84,X85,X86,X87,X88)=k3_enumset1(X84,X85,X86,X87,X88), inference(variable_rename,[status(thm)],[t80_enumset1])).
% 0.18/0.40  fof(c_0_28, negated_conjecture, (k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_xboole_0&esk2_0!=esk3_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.18/0.40  fof(c_0_29, plain, ![X94]:k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X94)=k1_tarski(X94), inference(variable_rename,[status(thm)],[t96_enumset1])).
% 0.18/0.40  cnf(c_0_30, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k1_enumset1(X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.40  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.40  cnf(c_0_32, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.40  fof(c_0_33, plain, ![X45, X46, X47, X48, X49, X50, X51]:k5_enumset1(X45,X46,X47,X48,X49,X50,X51)=k2_xboole_0(k2_enumset1(X45,X46,X47,X48),k1_enumset1(X49,X50,X51)), inference(variable_rename,[status(thm)],[l68_enumset1])).
% 0.18/0.40  fof(c_0_34, plain, ![X80, X81, X82, X83]:k3_enumset1(X80,X80,X81,X82,X83)=k2_enumset1(X80,X81,X82,X83), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.40  cnf(c_0_35, negated_conjecture, (k4_xboole_0(k1_tarski(esk2_0),k1_tarski(esk3_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.40  cnf(c_0_36, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.40  cnf(c_0_37, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.18/0.40  cnf(c_0_38, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_enumset1(X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.40  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.40  fof(c_0_40, plain, ![X11, X12, X13]:(~r1_tarski(X11,X12)|r1_tarski(k4_xboole_0(X11,X13),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t109_xboole_1])])).
% 0.18/0.40  cnf(c_0_41, negated_conjecture, (k4_xboole_0(k2_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)),k2_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.18/0.40  cnf(c_0_42, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X5,X6,X7))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39]), c_0_31]), c_0_32])).
% 0.18/0.40  cnf(c_0_43, plain, (r1_tarski(k4_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.18/0.40  cnf(c_0_44, negated_conjecture, (k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 0.18/0.40  fof(c_0_45, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.18/0.40  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.40  cnf(c_0_47, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.40  fof(c_0_48, plain, ![X22, X23]:k4_xboole_0(X22,k2_xboole_0(X22,X23))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.18/0.40  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_xboole_0,X1)|k4_xboole_0(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.40  cnf(c_0_50, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.40  fof(c_0_51, plain, ![X24, X25, X26]:k4_xboole_0(X24,k4_xboole_0(X25,X26))=k2_xboole_0(k4_xboole_0(X24,X25),k3_xboole_0(X24,X26)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.18/0.40  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(k1_xboole_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_44])).
% 0.18/0.40  cnf(c_0_54, plain, (r1_tarski(k1_xboole_0,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_50])).
% 0.18/0.40  cnf(c_0_55, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.40  cnf(c_0_56, negated_conjecture, (k4_xboole_0(k1_xboole_0,k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.40  cnf(c_0_57, plain, (r1_tarski(k1_xboole_0,X1)|k4_xboole_0(X2,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_47])).
% 0.18/0.40  fof(c_0_58, plain, ![X33, X34, X35]:k4_xboole_0(k5_xboole_0(X33,X34),X35)=k2_xboole_0(k4_xboole_0(X33,k2_xboole_0(X34,X35)),k4_xboole_0(X34,k2_xboole_0(X33,X35))), inference(variable_rename,[status(thm)],[t99_xboole_1])).
% 0.18/0.40  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1))=k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.40  cnf(c_0_60, plain, (r1_tarski(k1_xboole_0,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_50])).
% 0.18/0.40  cnf(c_0_61, plain, (k4_xboole_0(k5_xboole_0(X1,X2),X3)=k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X2,X3)),k4_xboole_0(X2,k2_xboole_0(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.40  cnf(c_0_62, negated_conjecture, (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k2_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1)))=k4_xboole_0(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_50])).
% 0.18/0.40  cnf(c_0_63, plain, (k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_60])).
% 0.18/0.40  cnf(c_0_64, plain, (k4_xboole_0(k5_xboole_0(X1,X1),X2)=k2_xboole_0(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_50]), c_0_50])).
% 0.18/0.40  cnf(c_0_65, negated_conjecture, (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_62])).
% 0.18/0.40  cnf(c_0_66, plain, (k4_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X2,X3)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_55])).
% 0.18/0.40  cnf(c_0_67, plain, (k2_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_64])).
% 0.18/0.40  fof(c_0_68, plain, ![X29]:k5_xboole_0(X29,k1_xboole_0)=X29, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.18/0.40  fof(c_0_69, plain, ![X30, X31, X32]:k2_xboole_0(k2_xboole_0(X30,X31),X32)=k2_xboole_0(k2_xboole_0(X30,X32),k2_xboole_0(X31,X32)), inference(variable_rename,[status(thm)],[t5_xboole_1])).
% 0.18/0.40  cnf(c_0_70, negated_conjecture, (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X1))), inference(spm,[status(thm)],[c_0_55, c_0_65])).
% 0.18/0.40  cnf(c_0_71, plain, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_66])).
% 0.18/0.40  cnf(c_0_72, plain, (k4_xboole_0(k5_xboole_0(X1,X1),X2)=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_67])).
% 0.18/0.40  cnf(c_0_73, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.18/0.40  cnf(c_0_74, plain, (k2_xboole_0(k2_xboole_0(X1,X2),X3)=k2_xboole_0(k2_xboole_0(X1,X3),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.18/0.40  cnf(c_0_75, negated_conjecture, (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.40  cnf(c_0_76, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.18/0.40  fof(c_0_77, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|r1_tarski(X14,k2_xboole_0(X16,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 0.18/0.40  cnf(c_0_78, plain, (k2_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0)=k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_74, c_0_67])).
% 0.18/0.40  cnf(c_0_79, negated_conjecture, (k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.18/0.40  cnf(c_0_80, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.18/0.40  cnf(c_0_81, negated_conjecture, (k2_xboole_0(k1_xboole_0,k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_67])).
% 0.18/0.40  cnf(c_0_82, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~r1_tarski(X1,k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.18/0.40  cnf(c_0_83, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(k2_xboole_0(X1,X3),X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_74])).
% 0.18/0.40  cnf(c_0_84, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|k4_xboole_0(X1,k2_xboole_0(k3_xboole_0(k1_xboole_0,X2),k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_47])).
% 0.18/0.40  fof(c_0_85, plain, ![X17, X18]:(k4_xboole_0(X17,X18)!=k4_xboole_0(X18,X17)|X17=X18), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.18/0.40  cnf(c_0_86, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k2_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_83, c_0_79])).
% 0.18/0.40  cnf(c_0_87, negated_conjecture, (r1_tarski(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_84, c_0_50])).
% 0.18/0.40  cnf(c_0_88, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.18/0.40  cnf(c_0_89, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_86]), c_0_73]), c_0_76]), c_0_67])).
% 0.18/0.40  fof(c_0_90, plain, ![X27, X28]:k4_xboole_0(k2_xboole_0(X27,X28),k3_xboole_0(X27,X28))=k2_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X28,X27)), inference(variable_rename,[status(thm)],[t55_xboole_1])).
% 0.18/0.40  cnf(c_0_91, negated_conjecture, (k4_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_87])).
% 0.18/0.40  cnf(c_0_92, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)=X1|k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.18/0.40  cnf(c_0_93, plain, (k4_xboole_0(X1,k2_xboole_0(X2,X3))=k1_xboole_0|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_52, c_0_80])).
% 0.18/0.40  cnf(c_0_94, plain, (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,X2))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.18/0.40  cnf(c_0_95, negated_conjecture, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_91]), c_0_76])])).
% 0.18/0.40  cnf(c_0_96, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)=X1|~r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.18/0.40  cnf(c_0_97, plain, (k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k1_xboole_0)=k4_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_67]), c_0_73]), c_0_63])).
% 0.18/0.40  cnf(c_0_98, plain, (k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0)=k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_67]), c_0_63])).
% 0.18/0.40  cnf(c_0_99, negated_conjecture, (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_76])).
% 0.18/0.40  cnf(c_0_100, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)=X1|k4_xboole_0(X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_47])).
% 0.18/0.40  cnf(c_0_101, plain, (k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_97])).
% 0.18/0.40  cnf(c_0_102, plain, (k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0)=k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0)), inference(rw,[status(thm)],[c_0_98, c_0_99])).
% 0.18/0.40  cnf(c_0_103, negated_conjecture, (k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0)=k4_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_99])).
% 0.18/0.40  cnf(c_0_104, plain, (k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),k1_xboole_0)=k4_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 0.18/0.40  cnf(c_0_105, plain, (r1_tarski(k4_xboole_0(X1,k1_xboole_0),X2)|~r1_tarski(k5_xboole_0(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_43, c_0_104])).
% 0.18/0.40  fof(c_0_106, plain, ![X19, X20, X21]:(~r1_tarski(k4_xboole_0(X19,X20),X21)|r1_tarski(X19,k2_xboole_0(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 0.18/0.40  cnf(c_0_107, plain, (r1_tarski(k4_xboole_0(X1,k1_xboole_0),X2)|k4_xboole_0(k5_xboole_0(k1_xboole_0,X1),X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_105, c_0_47])).
% 0.18/0.40  cnf(c_0_108, negated_conjecture, (k4_xboole_0(k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X1)),X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_86]), c_0_76]), c_0_67])).
% 0.18/0.40  cnf(c_0_109, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.18/0.40  cnf(c_0_110, negated_conjecture, (r1_tarski(k4_xboole_0(X1,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_103])).
% 0.18/0.40  cnf(c_0_111, negated_conjecture, (r1_tarski(X1,k2_xboole_0(k1_xboole_0,X1))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.18/0.40  cnf(c_0_112, negated_conjecture, (k4_xboole_0(X1,k2_xboole_0(k1_xboole_0,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_111])).
% 0.18/0.40  cnf(c_0_113, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|k4_xboole_0(k4_xboole_0(X1,X2),X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_109, c_0_47])).
% 0.18/0.40  cnf(c_0_114, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_112])])).
% 0.18/0.40  cnf(c_0_115, negated_conjecture, (r1_tarski(X1,X2)|k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.18/0.40  cnf(c_0_116, negated_conjecture, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_112, c_0_114])).
% 0.18/0.40  cnf(c_0_117, negated_conjecture, (k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_110])).
% 0.18/0.40  cnf(c_0_118, negated_conjecture, (r1_tarski(X1,k4_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 0.18/0.40  fof(c_0_119, plain, ![X95, X96]:((~r1_tarski(X95,k1_tarski(X96))|(X95=k1_xboole_0|X95=k1_tarski(X96)))&((X95!=k1_xboole_0|r1_tarski(X95,k1_tarski(X96)))&(X95!=k1_tarski(X96)|r1_tarski(X95,k1_tarski(X96))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.18/0.40  fof(c_0_120, plain, ![X65, X66, X67, X68, X69, X70, X71]:k5_enumset1(X65,X66,X67,X68,X69,X70,X71)=k2_xboole_0(k2_tarski(X65,X66),k3_enumset1(X67,X68,X69,X70,X71)), inference(variable_rename,[status(thm)],[t57_enumset1])).
% 0.18/0.40  fof(c_0_121, plain, ![X89, X90]:k3_enumset1(X89,X89,X89,X89,X90)=k2_tarski(X89,X90), inference(variable_rename,[status(thm)],[t83_enumset1])).
% 0.18/0.40  cnf(c_0_122, negated_conjecture, (k4_xboole_0(X1,k1_xboole_0)=X1|k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_117])).
% 0.18/0.40  cnf(c_0_123, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_118])).
% 0.18/0.40  fof(c_0_124, plain, ![X36, X37, X38, X39, X40, X41, X42, X43]:(((~r2_hidden(X39,X38)|(X39=X36|X39=X37)|X38!=k2_tarski(X36,X37))&((X40!=X36|r2_hidden(X40,X38)|X38!=k2_tarski(X36,X37))&(X40!=X37|r2_hidden(X40,X38)|X38!=k2_tarski(X36,X37))))&(((esk1_3(X41,X42,X43)!=X41|~r2_hidden(esk1_3(X41,X42,X43),X43)|X43=k2_tarski(X41,X42))&(esk1_3(X41,X42,X43)!=X42|~r2_hidden(esk1_3(X41,X42,X43),X43)|X43=k2_tarski(X41,X42)))&(r2_hidden(esk1_3(X41,X42,X43),X43)|(esk1_3(X41,X42,X43)=X41|esk1_3(X41,X42,X43)=X42)|X43=k2_tarski(X41,X42)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.18/0.40  cnf(c_0_125, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.18/0.40  cnf(c_0_126, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k2_tarski(X1,X2),k3_enumset1(X3,X4,X5,X6,X7))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.18/0.40  cnf(c_0_127, plain, (k3_enumset1(X1,X1,X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.18/0.40  cnf(c_0_128, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_72])).
% 0.18/0.40  cnf(c_0_129, negated_conjecture, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_123])])).
% 0.18/0.40  cnf(c_0_130, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.18/0.40  cnf(c_0_131, plain, (X1=k1_xboole_0|X1=k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))|~r1_tarski(X1,k2_xboole_0(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.18/0.40  cnf(c_0_132, plain, (k5_enumset1(X1,X2,X3,X4,X5,X6,X7)=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X4,X5,X6,X7))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_126, c_0_127]), c_0_32]), c_0_32])).
% 0.18/0.40  cnf(c_0_133, negated_conjecture, (r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k2_xboole_0(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_44]), c_0_128])])).
% 0.18/0.40  cnf(c_0_134, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_129]), c_0_129])).
% 0.18/0.40  cnf(c_0_135, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.18/0.40  cnf(c_0_136, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X2,X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_127]), c_0_32])).
% 0.18/0.40  cnf(c_0_137, plain, (X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|X1=k1_xboole_0|~r1_tarski(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_131, c_0_132]), c_0_132])).
% 0.18/0.40  cnf(c_0_138, negated_conjecture, (r1_tarski(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 0.18/0.40  cnf(c_0_139, plain, (X1=X4|X1=X3|X2!=k5_enumset1(X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_127]), c_0_32])).
% 0.18/0.40  cnf(c_0_140, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_136])])).
% 0.18/0.40  cnf(c_0_141, negated_conjecture, (k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)|k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_137, c_0_138])).
% 0.18/0.40  cnf(c_0_142, plain, (X1=X2|X1=X3|~r2_hidden(X1,k5_enumset1(X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_139])).
% 0.18/0.40  cnf(c_0_143, negated_conjecture, (k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0|r2_hidden(esk3_0,k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_140, c_0_141])).
% 0.18/0.40  cnf(c_0_144, negated_conjecture, (esk2_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.40  fof(c_0_145, plain, ![X60, X61, X62, X63, X64]:k3_enumset1(X60,X61,X62,X63,X64)=k2_xboole_0(k1_tarski(X60),k2_enumset1(X61,X62,X63,X64)), inference(variable_rename,[status(thm)],[t47_enumset1])).
% 0.18/0.40  fof(c_0_146, plain, ![X52, X53, X54, X55, X56, X57, X58, X59]:k6_enumset1(X52,X53,X54,X55,X56,X57,X58,X59)=k2_xboole_0(k2_enumset1(X52,X53,X54,X55),k2_enumset1(X56,X57,X58,X59)), inference(variable_rename,[status(thm)],[l75_enumset1])).
% 0.18/0.40  cnf(c_0_147, negated_conjecture, (k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_144])).
% 0.18/0.40  cnf(c_0_148, plain, (k3_enumset1(X1,X2,X3,X4,X5)=k2_xboole_0(k1_tarski(X1),k2_enumset1(X2,X3,X4,X5))), inference(split_conjunct,[status(thm)],[c_0_145])).
% 0.18/0.40  cnf(c_0_149, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_146])).
% 0.18/0.40  cnf(c_0_150, negated_conjecture, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k5_enumset1(X1,X2,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_147]), c_0_134])).
% 0.18/0.40  cnf(c_0_151, plain, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k2_xboole_0(k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)),k5_enumset1(X2,X2,X2,X2,X3,X4,X5))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_148, c_0_39]), c_0_36]), c_0_32]), c_0_32]), c_0_37])).
% 0.18/0.40  cnf(c_0_152, plain, (k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X2,X3),k5_enumset1(X4,X4,X4,X5,X6,X7,X8))=k2_xboole_0(k5_enumset1(X1,X1,X1,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X6,X7,X8))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_149, c_0_39]), c_0_39]), c_0_32]), c_0_32]), c_0_37])).
% 0.18/0.40  cnf(c_0_153, negated_conjecture, (X1=X2|X1=X3|~r2_hidden(X1,k5_enumset1(X3,X2,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_142, c_0_150])).
% 0.18/0.40  cnf(c_0_154, plain, (k5_enumset1(X1,X1,X2,X2,X3,X4,X5)=k5_enumset1(X1,X1,X1,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_151, c_0_42]), c_0_132])).
% 0.18/0.40  cnf(c_0_155, negated_conjecture, (k5_enumset1(X1,X1,X1,X2,X3,X4,X5)=k5_enumset1(esk2_0,X1,X2,X2,X3,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_152, c_0_147]), c_0_114]), c_0_132])).
% 0.18/0.40  cnf(c_0_156, negated_conjecture, (X1=X2|~r2_hidden(X1,k5_enumset1(X2,X2,X2,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_153, c_0_154])).
% 0.18/0.40  cnf(c_0_157, negated_conjecture, (r2_hidden(X1,k5_enumset1(esk2_0,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_140, c_0_155])).
% 0.18/0.40  cnf(c_0_158, negated_conjecture, (X1=X2|~r2_hidden(X1,k5_enumset1(esk2_0,X2,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_156, c_0_155])).
% 0.18/0.40  cnf(c_0_159, negated_conjecture, (r2_hidden(esk2_0,k5_enumset1(esk2_0,X1,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_157, c_0_150])).
% 0.18/0.40  cnf(c_0_160, negated_conjecture, (esk2_0=X1), inference(spm,[status(thm)],[c_0_158, c_0_159])).
% 0.18/0.40  cnf(c_0_161, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144, c_0_160])]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 162
% 0.18/0.40  # Proof object clause steps            : 113
% 0.18/0.40  # Proof object formula steps           : 49
% 0.18/0.40  # Proof object conjectures             : 56
% 0.18/0.40  # Proof object clause conjectures      : 53
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 27
% 0.18/0.40  # Proof object initial formulas used   : 24
% 0.18/0.40  # Proof object generating inferences   : 62
% 0.18/0.40  # Proof object simplifying inferences  : 74
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 24
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 33
% 0.18/0.40  # Removed in clause preprocessing      : 6
% 0.18/0.40  # Initial clauses in saturation        : 27
% 0.18/0.40  # Processed clauses                    : 312
% 0.18/0.40  # ...of these trivial                  : 29
% 0.18/0.40  # ...subsumed                          : 72
% 0.18/0.40  # ...remaining for further processing  : 211
% 0.18/0.40  # Other redundant clauses eliminated   : 17
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 4
% 0.18/0.40  # Backward-rewritten                   : 169
% 0.18/0.40  # Generated clauses                    : 2137
% 0.18/0.40  # ...of the previous two non-trivial   : 1573
% 0.18/0.40  # Contextual simplify-reflections      : 0
% 0.18/0.40  # Paramodulations                      : 2121
% 0.18/0.40  # Factorizations                       : 0
% 0.18/0.40  # Equation resolutions                 : 18
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 6
% 0.18/0.40  #    Positive orientable unit clauses  : 3
% 0.18/0.40  #    Positive unorientable unit clauses: 1
% 0.18/0.40  #    Negative unit clauses             : 0
% 0.18/0.40  #    Non-unit-clauses                  : 2
% 0.18/0.40  # Current number of unprocessed clauses: 1131
% 0.18/0.40  # ...number of literals in the above   : 2345
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 206
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 304
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 282
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 74
% 0.18/0.40  # Unit Clause-clause subsumption calls : 126
% 0.18/0.40  # Rewrite failures with RHS unbound    : 5
% 0.18/0.40  # BW rewrite match attempts            : 385
% 0.18/0.40  # BW rewrite match successes           : 221
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 25733
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.064 s
% 0.18/0.40  # System time              : 0.005 s
% 0.18/0.40  # Total time               : 0.069 s
% 0.18/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
