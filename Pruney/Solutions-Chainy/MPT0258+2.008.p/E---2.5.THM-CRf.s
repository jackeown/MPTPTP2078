%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:49 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 675 expanded)
%              Number of clauses        :   41 ( 244 expanded)
%              Number of leaves         :   20 ( 214 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 711 expanded)
%              Number of equality atoms :   74 ( 667 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t53_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r2_hidden(X3,X2) )
     => k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(t95_xboole_1,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

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

fof(t125_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(t55_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t66_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7,X8] : k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(commutativity_k5_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(t91_xboole_1,axiom,(
    ! [X1,X2,X3] : k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(c_0_20,plain,(
    ! [X66,X67] : k3_tarski(k2_tarski(X66,X67)) = k2_xboole_0(X66,X67) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X39,X40] : k1_enumset1(X39,X39,X40) = k2_tarski(X39,X40) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r2_hidden(X1,X2)
          & r2_hidden(X3,X2) )
       => k3_xboole_0(k2_tarski(X1,X3),X2) = k2_tarski(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t53_zfmisc_1])).

fof(c_0_23,plain,(
    ! [X18,X19] : k3_xboole_0(X18,X19) = k5_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)) ),
    inference(variable_rename,[status(thm)],[t95_xboole_1])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X41,X42,X43] : k2_enumset1(X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X44,X45,X46,X47] : k3_enumset1(X44,X44,X45,X46,X47) = k2_enumset1(X44,X45,X46,X47) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0)
    & r2_hidden(esk3_0,esk2_0)
    & k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != k2_tarski(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X48,X49,X50,X51,X52] : k4_enumset1(X48,X48,X49,X50,X51,X52) = k3_enumset1(X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_34,plain,(
    ! [X53,X54,X55,X56,X57,X58] : k5_enumset1(X53,X53,X54,X55,X56,X57,X58) = k4_enumset1(X53,X54,X55,X56,X57,X58) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_35,plain,(
    ! [X59,X60,X61,X62,X63,X64,X65] : k6_enumset1(X59,X59,X60,X61,X62,X63,X64,X65) = k5_enumset1(X59,X60,X61,X62,X63,X64,X65) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_36,plain,(
    ! [X20,X21,X22,X23] : k2_enumset1(X20,X21,X22,X23) = k2_enumset1(X23,X22,X21,X20) ),
    inference(variable_rename,[status(thm)],[t125_enumset1])).

fof(c_0_37,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k4_enumset1(X24,X25,X26,X27,X28,X29) = k2_xboole_0(k3_enumset1(X24,X25,X26,X27,X28),k1_tarski(X29)) ),
    inference(variable_rename,[status(thm)],[t55_enumset1])).

fof(c_0_38,plain,(
    ! [X38] : k2_tarski(X38,X38) = k1_tarski(X38) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] : k6_enumset1(X30,X31,X32,X33,X34,X35,X36,X37) = k2_xboole_0(k3_enumset1(X30,X31,X32,X33,X34),k1_enumset1(X35,X36,X37)) ),
    inference(variable_rename,[status(thm)],[t66_enumset1])).

fof(c_0_40,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k2_xboole_0(X12,X13) = X13 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

fof(c_0_41,plain,(
    ! [X11] : k3_xboole_0(X11,X11) = X11 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_42,plain,(
    ! [X68] : k3_tarski(k1_tarski(X68)) = X68 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_43,negated_conjecture,
    ( k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0) != k2_tarski(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_48,plain,(
    ! [X9,X10] : k5_xboole_0(X9,X10) = k5_xboole_0(X10,X9) ),
    inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).

cnf(c_0_49,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_enumset1(X4,X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_50,plain,(
    ! [X14,X15,X16] : k5_xboole_0(k5_xboole_0(X14,X15),X16) = k5_xboole_0(X14,k5_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t91_xboole_1])).

cnf(c_0_51,plain,
    ( k4_enumset1(X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_56,plain,(
    ! [X17] : k5_xboole_0(X17,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_57,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0),k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_25]),c_0_25]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47])).

cnf(c_0_59,plain,
    ( k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4) = k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_32]),c_0_32]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_61,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X2),X3) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52]),c_0_25]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47])).

cnf(c_0_63,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_46]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47]),c_0_47])).

cnf(c_0_64,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_30]),c_0_31]),c_0_32]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_65,plain,
    ( k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_66,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_52]),c_0_25]),c_0_31]),c_0_32]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_68,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61])).

cnf(c_0_69,plain,
    ( k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X6) = k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X2,X2,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_60])).

cnf(c_0_71,plain,
    ( k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

fof(c_0_72,plain,(
    ! [X69,X70,X71] :
      ( ( r2_hidden(X69,X71)
        | ~ r1_tarski(k2_tarski(X69,X70),X71) )
      & ( r2_hidden(X70,X71)
        | ~ r1_tarski(k2_tarski(X69,X70),X71) )
      & ( ~ r2_hidden(X69,X71)
        | ~ r2_hidden(X70,X71)
        | r1_tarski(k2_tarski(X69,X70),X71) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_73,negated_conjecture,
    ( k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0))))) != k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_69])).

cnf(c_0_75,plain,
    ( k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_66]),c_0_71])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( ~ r1_tarski(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_59]),c_0_75])])).

cnf(c_0_78,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_25]),c_0_31]),c_0_32]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:41:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(t53_zfmisc_1, conjecture, ![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 0.19/0.39  fof(t95_xboole_1, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 0.19/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.39  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.39  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.39  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.39  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.19/0.39  fof(t125_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_enumset1)).
% 0.19/0.39  fof(t55_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_enumset1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t66_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7, X8]:k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_enumset1)).
% 0.19/0.39  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.39  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.39  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 0.19/0.39  fof(commutativity_k5_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 0.19/0.39  fof(t91_xboole_1, axiom, ![X1, X2, X3]:k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 0.19/0.39  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.19/0.39  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.19/0.39  fof(c_0_20, plain, ![X66, X67]:k3_tarski(k2_tarski(X66,X67))=k2_xboole_0(X66,X67), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.39  fof(c_0_21, plain, ![X39, X40]:k1_enumset1(X39,X39,X40)=k2_tarski(X39,X40), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3]:((r2_hidden(X1,X2)&r2_hidden(X3,X2))=>k3_xboole_0(k2_tarski(X1,X3),X2)=k2_tarski(X1,X3))), inference(assume_negation,[status(cth)],[t53_zfmisc_1])).
% 0.19/0.39  fof(c_0_23, plain, ![X18, X19]:k3_xboole_0(X18,X19)=k5_xboole_0(k5_xboole_0(X18,X19),k2_xboole_0(X18,X19)), inference(variable_rename,[status(thm)],[t95_xboole_1])).
% 0.19/0.39  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  fof(c_0_26, plain, ![X41, X42, X43]:k2_enumset1(X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.39  fof(c_0_27, plain, ![X44, X45, X46, X47]:k3_enumset1(X44,X44,X45,X46,X47)=k2_enumset1(X44,X45,X46,X47), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.39  fof(c_0_28, negated_conjecture, ((r2_hidden(esk1_0,esk2_0)&r2_hidden(esk3_0,esk2_0))&k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)!=k2_tarski(esk1_0,esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.39  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_30, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.39  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.39  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  fof(c_0_33, plain, ![X48, X49, X50, X51, X52]:k4_enumset1(X48,X48,X49,X50,X51,X52)=k3_enumset1(X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.39  fof(c_0_34, plain, ![X53, X54, X55, X56, X57, X58]:k5_enumset1(X53,X53,X54,X55,X56,X57,X58)=k4_enumset1(X53,X54,X55,X56,X57,X58), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.39  fof(c_0_35, plain, ![X59, X60, X61, X62, X63, X64, X65]:k6_enumset1(X59,X59,X60,X61,X62,X63,X64,X65)=k5_enumset1(X59,X60,X61,X62,X63,X64,X65), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.19/0.39  fof(c_0_36, plain, ![X20, X21, X22, X23]:k2_enumset1(X20,X21,X22,X23)=k2_enumset1(X23,X22,X21,X20), inference(variable_rename,[status(thm)],[t125_enumset1])).
% 0.19/0.39  fof(c_0_37, plain, ![X24, X25, X26, X27, X28, X29]:k4_enumset1(X24,X25,X26,X27,X28,X29)=k2_xboole_0(k3_enumset1(X24,X25,X26,X27,X28),k1_tarski(X29)), inference(variable_rename,[status(thm)],[t55_enumset1])).
% 0.19/0.39  fof(c_0_38, plain, ![X38]:k2_tarski(X38,X38)=k1_tarski(X38), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_39, plain, ![X30, X31, X32, X33, X34, X35, X36, X37]:k6_enumset1(X30,X31,X32,X33,X34,X35,X36,X37)=k2_xboole_0(k3_enumset1(X30,X31,X32,X33,X34),k1_enumset1(X35,X36,X37)), inference(variable_rename,[status(thm)],[t66_enumset1])).
% 0.19/0.39  fof(c_0_40, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k2_xboole_0(X12,X13)=X13), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.39  fof(c_0_41, plain, ![X11]:k3_xboole_0(X11,X11)=X11, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.39  fof(c_0_42, plain, ![X68]:k3_tarski(k1_tarski(X68))=X68, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (k3_xboole_0(k2_tarski(esk1_0,esk3_0),esk2_0)!=k2_tarski(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k5_xboole_0(k5_xboole_0(X1,X2),k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.19/0.39  cnf(c_0_45, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_46, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.39  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  fof(c_0_48, plain, ![X9, X10]:k5_xboole_0(X9,X10)=k5_xboole_0(X10,X9), inference(variable_rename,[status(thm)],[commutativity_k5_xboole_0])).
% 0.19/0.39  cnf(c_0_49, plain, (k2_enumset1(X1,X2,X3,X4)=k2_enumset1(X4,X3,X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  fof(c_0_50, plain, ![X14, X15, X16]:k5_xboole_0(k5_xboole_0(X14,X15),X16)=k5_xboole_0(X14,k5_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t91_xboole_1])).
% 0.19/0.39  cnf(c_0_51, plain, (k4_enumset1(X1,X2,X3,X4,X5,X6)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X6))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.39  cnf(c_0_52, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.39  cnf(c_0_53, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  cnf(c_0_54, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.39  cnf(c_0_55, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.39  fof(c_0_56, plain, ![X17]:k5_xboole_0(X17,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.19/0.39  cnf(c_0_57, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (k5_xboole_0(k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0),k3_tarski(k6_enumset1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0)))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_25]), c_0_25]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47])).
% 0.19/0.39  cnf(c_0_59, plain, (k5_xboole_0(X1,X2)=k5_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.39  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4)=k6_enumset1(X4,X4,X4,X4,X4,X3,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_32]), c_0_32]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.19/0.39  cnf(c_0_61, plain, (k5_xboole_0(k5_xboole_0(X1,X2),X3)=k5_xboole_0(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  cnf(c_0_62, plain, (k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52]), c_0_25]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47])).
% 0.19/0.39  cnf(c_0_63, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)=k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X1,X1,X1,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X7,X8)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_46]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47]), c_0_47])).
% 0.19/0.39  cnf(c_0_64, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_30]), c_0_31]), c_0_32]), c_0_45]), c_0_46]), c_0_47])).
% 0.19/0.39  cnf(c_0_65, plain, (k5_xboole_0(k5_xboole_0(X1,X1),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.19/0.39  cnf(c_0_66, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.39  cnf(c_0_67, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_52]), c_0_25]), c_0_31]), c_0_32]), c_0_45]), c_0_46]), c_0_47])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61])).
% 0.19/0.39  cnf(c_0_69, plain, (k6_enumset1(X1,X2,X3,X4,X5,X6,X6,X6)=k6_enumset1(X1,X1,X1,X2,X3,X4,X5,X6)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.39  cnf(c_0_70, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X2,X2,X2))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_64, c_0_60])).
% 0.19/0.39  cnf(c_0_71, plain, (k5_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.19/0.39  fof(c_0_72, plain, ![X69, X70, X71]:(((r2_hidden(X69,X71)|~r1_tarski(k2_tarski(X69,X70),X71))&(r2_hidden(X70,X71)|~r1_tarski(k2_tarski(X69,X70),X71)))&(~r2_hidden(X69,X71)|~r2_hidden(X70,X71)|r1_tarski(k2_tarski(X69,X70),X71))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.19/0.39  cnf(c_0_73, negated_conjecture, (k5_xboole_0(esk2_0,k5_xboole_0(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),k3_tarski(k6_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)))))!=k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.39  cnf(c_0_74, plain, (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))=X1|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_70, c_0_69])).
% 0.19/0.39  cnf(c_0_75, plain, (k5_xboole_0(X1,k5_xboole_0(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_66]), c_0_71])).
% 0.19/0.39  cnf(c_0_76, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (~r1_tarski(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_59]), c_0_75])])).
% 0.19/0.39  cnf(c_0_78, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X3),X2)|~r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_25]), c_0_31]), c_0_32]), c_0_45]), c_0_46]), c_0_47])).
% 0.19/0.39  cnf(c_0_79, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (r2_hidden(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_80])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 82
% 0.19/0.39  # Proof object clause steps            : 41
% 0.19/0.39  # Proof object formula steps           : 41
% 0.19/0.39  # Proof object conjectures             : 11
% 0.19/0.39  # Proof object clause conjectures      : 8
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 22
% 0.19/0.39  # Proof object initial formulas used   : 20
% 0.19/0.39  # Proof object generating inferences   : 5
% 0.19/0.39  # Proof object simplifying inferences  : 136
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 20
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 24
% 0.19/0.39  # Removed in clause preprocessing      : 9
% 0.19/0.39  # Initial clauses in saturation        : 15
% 0.19/0.39  # Processed clauses                    : 536
% 0.19/0.39  # ...of these trivial                  : 67
% 0.19/0.39  # ...subsumed                          : 383
% 0.19/0.39  # ...remaining for further processing  : 86
% 0.19/0.39  # Other redundant clauses eliminated   : 0
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 1806
% 0.19/0.39  # ...of the previous two non-trivial   : 1374
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 1806
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 0
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 70
% 0.19/0.39  #    Positive orientable unit clauses  : 19
% 0.19/0.39  #    Positive unorientable unit clauses: 12
% 0.19/0.39  #    Negative unit clauses             : 2
% 0.19/0.39  #    Non-unit-clauses                  : 37
% 0.19/0.39  # Current number of unprocessed clauses: 864
% 0.19/0.39  # ...number of literals in the above   : 1228
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 25
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1542
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1542
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 218
% 0.19/0.39  # Unit Clause-clause subsumption calls : 74
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 658
% 0.19/0.39  # BW rewrite match successes           : 301
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 13377
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.050 s
% 0.19/0.39  # System time              : 0.005 s
% 0.19/0.39  # Total time               : 0.055 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
