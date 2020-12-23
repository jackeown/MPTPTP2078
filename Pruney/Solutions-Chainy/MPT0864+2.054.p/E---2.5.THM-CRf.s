%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:59:25 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 690 expanded)
%              Number of clauses        :   49 ( 263 expanded)
%              Number of leaves         :   19 ( 211 expanded)
%              Depth                    :   12
%              Number of atoms          :  182 ( 891 expanded)
%              Number of equality atoms :  145 ( 821 expanded)
%              Maximal formula depth    :   37 (   3 average)
%              Maximal clause size      :   52 (   1 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

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

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(t20_mcart_1,conjecture,(
    ! [X1] :
      ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
     => ( X1 != k1_mcart_1(X1)
        & X1 != k2_mcart_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(t36_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))
      & k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(t7_mcart_1,axiom,(
    ! [X1,X2] :
      ( k1_mcart_1(k4_tarski(X1,X2)) = X1
      & k2_mcart_1(k4_tarski(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(c_0_19,plain,(
    ! [X64,X65] : k1_setfam_1(k2_tarski(X64,X65)) = k3_xboole_0(X64,X65) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_20,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X11,X12] : k4_xboole_0(X11,X12) = k5_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

cnf(c_0_22,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X38,X39] : k3_tarski(k2_tarski(X38,X39)) = k2_xboole_0(X38,X39) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_25,plain,(
    ! [X42,X43] :
      ( ( k4_xboole_0(k1_tarski(X42),k1_tarski(X43)) != k1_tarski(X42)
        | X42 != X43 )
      & ( X42 = X43
        | k4_xboole_0(k1_tarski(X42),k1_tarski(X43)) = k1_tarski(X42) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_26,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_29,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X21,X22,X23,X24] : k3_enumset1(X21,X21,X22,X23,X24) = k2_enumset1(X21,X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X25,X26,X27,X28,X29] : k4_enumset1(X25,X25,X26,X27,X28,X29) = k3_enumset1(X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_32,plain,(
    ! [X30,X31,X32,X33,X34,X35] : k5_enumset1(X30,X30,X31,X32,X33,X34,X35) = k4_enumset1(X30,X31,X32,X33,X34,X35) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_33,plain,(
    ! [X10] : k3_xboole_0(X10,X10) = X10 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_34,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k2_xboole_0(X13,X14)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

cnf(c_0_35,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X9] : k2_xboole_0(X9,X9) = X9 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

fof(c_0_37,negated_conjecture,(
    ~ ! [X1] :
        ( ? [X2,X3] : X1 = k4_tarski(X2,X3)
       => ( X1 != k1_mcart_1(X1)
          & X1 != k2_mcart_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t20_mcart_1])).

fof(c_0_38,plain,(
    ! [X44,X45,X46] :
      ( k2_zfmisc_1(k1_tarski(X44),k2_tarski(X45,X46)) = k2_tarski(k4_tarski(X44,X45),k4_tarski(X44,X46))
      & k2_zfmisc_1(k2_tarski(X44,X45),k1_tarski(X46)) = k2_tarski(k4_tarski(X44,X46),k4_tarski(X45,X46)) ) ),
    inference(variable_rename,[status(thm)],[t36_zfmisc_1])).

cnf(c_0_39,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_23])).

cnf(c_0_49,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_50,plain,(
    ! [X66,X67] :
      ( k1_mcart_1(k4_tarski(X66,X67)) = X66
      & k2_mcart_1(k4_tarski(X66,X67)) = X67 ) ),
    inference(variable_rename,[status(thm)],[t7_mcart_1])).

fof(c_0_51,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0)
    & ( esk2_0 = k1_mcart_1(esk2_0)
      | esk2_0 = k2_mcart_1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).

fof(c_0_52,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61,X62] :
      ( ( ~ r2_hidden(X54,X53)
        | X54 = X47
        | X54 = X48
        | X54 = X49
        | X54 = X50
        | X54 = X51
        | X54 = X52
        | X53 != k4_enumset1(X47,X48,X49,X50,X51,X52) )
      & ( X55 != X47
        | r2_hidden(X55,X53)
        | X53 != k4_enumset1(X47,X48,X49,X50,X51,X52) )
      & ( X55 != X48
        | r2_hidden(X55,X53)
        | X53 != k4_enumset1(X47,X48,X49,X50,X51,X52) )
      & ( X55 != X49
        | r2_hidden(X55,X53)
        | X53 != k4_enumset1(X47,X48,X49,X50,X51,X52) )
      & ( X55 != X50
        | r2_hidden(X55,X53)
        | X53 != k4_enumset1(X47,X48,X49,X50,X51,X52) )
      & ( X55 != X51
        | r2_hidden(X55,X53)
        | X53 != k4_enumset1(X47,X48,X49,X50,X51,X52) )
      & ( X55 != X52
        | r2_hidden(X55,X53)
        | X53 != k4_enumset1(X47,X48,X49,X50,X51,X52) )
      & ( esk1_7(X56,X57,X58,X59,X60,X61,X62) != X56
        | ~ r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k4_enumset1(X56,X57,X58,X59,X60,X61) )
      & ( esk1_7(X56,X57,X58,X59,X60,X61,X62) != X57
        | ~ r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k4_enumset1(X56,X57,X58,X59,X60,X61) )
      & ( esk1_7(X56,X57,X58,X59,X60,X61,X62) != X58
        | ~ r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k4_enumset1(X56,X57,X58,X59,X60,X61) )
      & ( esk1_7(X56,X57,X58,X59,X60,X61,X62) != X59
        | ~ r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k4_enumset1(X56,X57,X58,X59,X60,X61) )
      & ( esk1_7(X56,X57,X58,X59,X60,X61,X62) != X60
        | ~ r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k4_enumset1(X56,X57,X58,X59,X60,X61) )
      & ( esk1_7(X56,X57,X58,X59,X60,X61,X62) != X61
        | ~ r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)
        | X62 = k4_enumset1(X56,X57,X58,X59,X60,X61) )
      & ( r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)
        | esk1_7(X56,X57,X58,X59,X60,X61,X62) = X56
        | esk1_7(X56,X57,X58,X59,X60,X61,X62) = X57
        | esk1_7(X56,X57,X58,X59,X60,X61,X62) = X58
        | esk1_7(X56,X57,X58,X59,X60,X61,X62) = X59
        | esk1_7(X56,X57,X58,X59,X60,X61,X62) = X60
        | esk1_7(X56,X57,X58,X59,X60,X61,X62) = X61
        | X62 = k4_enumset1(X56,X57,X58,X59,X60,X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)) = k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_54,plain,
    ( X1 != X2
    | k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2)))) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40]),c_0_40]),c_0_23]),c_0_23]),c_0_23]),c_0_41]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_55,plain,
    ( k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_28]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_56,plain,
    ( k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45])).

cnf(c_0_57,plain,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_48]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_58,plain,
    ( k1_mcart_1(k4_tarski(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k4_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_60,plain,(
    ! [X36,X37] :
      ( ( ~ r1_tarski(k1_tarski(X36),X37)
        | r2_hidden(X36,X37) )
      & ( ~ r2_hidden(X36,X37)
        | r1_tarski(k1_tarski(X36),X37) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X4,X5,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_62,plain,(
    ! [X40,X41] :
      ( ( ~ r1_tarski(X40,k2_zfmisc_1(X40,X41))
        | X40 = k1_xboole_0 )
      & ( ~ r1_tarski(X40,k2_zfmisc_1(X41,X40))
        | X40 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) = k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_40]),c_0_23]),c_0_23]),c_0_23]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_64,plain,
    ( k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) != k5_enumset1(X1,X1,X1,X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_54]),c_0_55])).

cnf(c_0_65,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( esk2_0 = k1_mcart_1(esk2_0)
    | esk2_0 = k2_mcart_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_67,negated_conjecture,
    ( k1_mcart_1(esk2_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_68,plain,
    ( k2_mcart_1(k4_tarski(X1,X2)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X2,X2,X4,X5,X6,X7,X8) ),
    inference(rw,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( k2_zfmisc_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) = k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k4_tarski(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_59])).

cnf(c_0_73,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk2_0
    | esk3_0 = esk2_0 ),
    inference(rw,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_75,negated_conjecture,
    ( k2_mcart_1(esk2_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_59])).

cnf(c_0_76,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_40]),c_0_23]),c_0_42]),c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k5_enumset1(X1,X1,X2,X3,X4,X5,X6)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k4_tarski(X1,esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( esk3_0 = esk2_0
    | esk4_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,plain,
    ( r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X2,X3,X4,X5,X6)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_82,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) = k5_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_40]),c_0_23]),c_0_23]),c_0_23]),c_0_42]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_45])).

cnf(c_0_84,negated_conjecture,
    ( k4_tarski(esk2_0,esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_59,c_0_82])).

cnf(c_0_85,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_86,negated_conjecture,
    ( k2_zfmisc_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1)) = k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k4_tarski(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_80])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.19/0.37  # and selection function SelectNegativeLiterals.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.029 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.19/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.37  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.19/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.19/0.37  fof(idempotence_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 0.19/0.37  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.19/0.37  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.19/0.37  fof(t20_mcart_1, conjecture, ![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 0.19/0.37  fof(t36_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))&k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 0.19/0.37  fof(t7_mcart_1, axiom, ![X1, X2]:(k1_mcart_1(k4_tarski(X1,X2))=X1&k2_mcart_1(k4_tarski(X1,X2))=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 0.19/0.37  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_enumset1)).
% 0.19/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.37  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.19/0.37  fof(c_0_19, plain, ![X64, X65]:k1_setfam_1(k2_tarski(X64,X65))=k3_xboole_0(X64,X65), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.37  fof(c_0_20, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_21, plain, ![X11, X12]:k4_xboole_0(X11,X12)=k5_xboole_0(X11,k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.19/0.37  cnf(c_0_22, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  fof(c_0_24, plain, ![X38, X39]:k3_tarski(k2_tarski(X38,X39))=k2_xboole_0(X38,X39), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.37  fof(c_0_25, plain, ![X42, X43]:((k4_xboole_0(k1_tarski(X42),k1_tarski(X43))!=k1_tarski(X42)|X42!=X43)&(X42=X43|k4_xboole_0(k1_tarski(X42),k1_tarski(X43))=k1_tarski(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.19/0.37  fof(c_0_26, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_28, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  fof(c_0_29, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  fof(c_0_30, plain, ![X21, X22, X23, X24]:k3_enumset1(X21,X21,X22,X23,X24)=k2_enumset1(X21,X22,X23,X24), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.37  fof(c_0_31, plain, ![X25, X26, X27, X28, X29]:k4_enumset1(X25,X25,X26,X27,X28,X29)=k3_enumset1(X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.19/0.37  fof(c_0_32, plain, ![X30, X31, X32, X33, X34, X35]:k5_enumset1(X30,X30,X31,X32,X33,X34,X35)=k4_enumset1(X30,X31,X32,X33,X34,X35), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.19/0.37  fof(c_0_33, plain, ![X10]:k3_xboole_0(X10,X10)=X10, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).
% 0.19/0.37  fof(c_0_34, plain, ![X13, X14]:k4_xboole_0(X13,k2_xboole_0(X13,X14))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.19/0.37  cnf(c_0_35, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  fof(c_0_36, plain, ![X9]:k2_xboole_0(X9,X9)=X9, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.19/0.37  fof(c_0_37, negated_conjecture, ~(![X1]:(?[X2, X3]:X1=k4_tarski(X2,X3)=>(X1!=k1_mcart_1(X1)&X1!=k2_mcart_1(X1)))), inference(assume_negation,[status(cth)],[t20_mcart_1])).
% 0.19/0.37  fof(c_0_38, plain, ![X44, X45, X46]:(k2_zfmisc_1(k1_tarski(X44),k2_tarski(X45,X46))=k2_tarski(k4_tarski(X44,X45),k4_tarski(X44,X46))&k2_zfmisc_1(k2_tarski(X44,X45),k1_tarski(X46))=k2_tarski(k4_tarski(X44,X46),k4_tarski(X45,X46))), inference(variable_rename,[status(thm)],[t36_zfmisc_1])).
% 0.19/0.37  cnf(c_0_39, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_41, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.37  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_45, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_46, plain, (k3_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  cnf(c_0_47, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_48, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_23])).
% 0.19/0.37  cnf(c_0_49, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.37  fof(c_0_50, plain, ![X66, X67]:(k1_mcart_1(k4_tarski(X66,X67))=X66&k2_mcart_1(k4_tarski(X66,X67))=X67), inference(variable_rename,[status(thm)],[t7_mcart_1])).
% 0.19/0.37  fof(c_0_51, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)&(esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_37])])])).
% 0.19/0.37  fof(c_0_52, plain, ![X47, X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61, X62]:(((~r2_hidden(X54,X53)|(X54=X47|X54=X48|X54=X49|X54=X50|X54=X51|X54=X52)|X53!=k4_enumset1(X47,X48,X49,X50,X51,X52))&((((((X55!=X47|r2_hidden(X55,X53)|X53!=k4_enumset1(X47,X48,X49,X50,X51,X52))&(X55!=X48|r2_hidden(X55,X53)|X53!=k4_enumset1(X47,X48,X49,X50,X51,X52)))&(X55!=X49|r2_hidden(X55,X53)|X53!=k4_enumset1(X47,X48,X49,X50,X51,X52)))&(X55!=X50|r2_hidden(X55,X53)|X53!=k4_enumset1(X47,X48,X49,X50,X51,X52)))&(X55!=X51|r2_hidden(X55,X53)|X53!=k4_enumset1(X47,X48,X49,X50,X51,X52)))&(X55!=X52|r2_hidden(X55,X53)|X53!=k4_enumset1(X47,X48,X49,X50,X51,X52))))&(((((((esk1_7(X56,X57,X58,X59,X60,X61,X62)!=X56|~r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)|X62=k4_enumset1(X56,X57,X58,X59,X60,X61))&(esk1_7(X56,X57,X58,X59,X60,X61,X62)!=X57|~r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)|X62=k4_enumset1(X56,X57,X58,X59,X60,X61)))&(esk1_7(X56,X57,X58,X59,X60,X61,X62)!=X58|~r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)|X62=k4_enumset1(X56,X57,X58,X59,X60,X61)))&(esk1_7(X56,X57,X58,X59,X60,X61,X62)!=X59|~r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)|X62=k4_enumset1(X56,X57,X58,X59,X60,X61)))&(esk1_7(X56,X57,X58,X59,X60,X61,X62)!=X60|~r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)|X62=k4_enumset1(X56,X57,X58,X59,X60,X61)))&(esk1_7(X56,X57,X58,X59,X60,X61,X62)!=X61|~r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)|X62=k4_enumset1(X56,X57,X58,X59,X60,X61)))&(r2_hidden(esk1_7(X56,X57,X58,X59,X60,X61,X62),X62)|(esk1_7(X56,X57,X58,X59,X60,X61,X62)=X56|esk1_7(X56,X57,X58,X59,X60,X61,X62)=X57|esk1_7(X56,X57,X58,X59,X60,X61,X62)=X58|esk1_7(X56,X57,X58,X59,X60,X61,X62)=X59|esk1_7(X56,X57,X58,X59,X60,X61,X62)=X60|esk1_7(X56,X57,X58,X59,X60,X61,X62)=X61)|X62=k4_enumset1(X56,X57,X58,X59,X60,X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.19/0.37  cnf(c_0_53, plain, (k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))=k2_tarski(k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.37  cnf(c_0_54, plain, (X1!=X2|k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k5_enumset1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X2))))!=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_40]), c_0_40]), c_0_23]), c_0_23]), c_0_23]), c_0_41]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45]), c_0_45])).
% 0.19/0.38  cnf(c_0_55, plain, (k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_28]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_56, plain, (k5_xboole_0(X1,k1_setfam_1(k5_enumset1(X1,X1,X1,X1,X1,X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2)))))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45])).
% 0.19/0.38  cnf(c_0_57, plain, (k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_48]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_58, plain, (k1_mcart_1(k4_tarski(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (esk2_0=k4_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.38  fof(c_0_60, plain, ![X36, X37]:((~r1_tarski(k1_tarski(X36),X37)|r2_hidden(X36,X37))&(~r2_hidden(X36,X37)|r1_tarski(k1_tarski(X36),X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.38  cnf(c_0_61, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X4,X5,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.38  fof(c_0_62, plain, ![X40, X41]:((~r1_tarski(X40,k2_zfmisc_1(X40,X41))|X40=k1_xboole_0)&(~r1_tarski(X40,k2_zfmisc_1(X41,X40))|X40=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_63, plain, (k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k5_enumset1(X3,X3,X3,X3,X3,X3,X3))=k5_enumset1(k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X1,X3),k4_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_40]), c_0_23]), c_0_23]), c_0_23]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45])).
% 0.19/0.38  cnf(c_0_64, plain, (k5_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X1))!=k5_enumset1(X1,X1,X1,X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_54]), c_0_55])).
% 0.19/0.38  cnf(c_0_65, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_55])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (esk2_0=k1_mcart_1(esk2_0)|esk2_0=k2_mcart_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (k1_mcart_1(esk2_0)=esk3_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.38  cnf(c_0_68, plain, (k2_mcart_1(k4_tarski(X1,X2))=X2), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_69, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.38  cnf(c_0_70, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X2,X2,X4,X5,X6,X7,X8)), inference(rw,[status(thm)],[c_0_61, c_0_45])).
% 0.19/0.38  cnf(c_0_71, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, (k2_zfmisc_1(k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,X1),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k4_tarski(X1,esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_59])).
% 0.19/0.38  cnf(c_0_73, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.38  cnf(c_0_74, negated_conjecture, (k2_mcart_1(esk2_0)=esk2_0|esk3_0=esk2_0), inference(rw,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.38  cnf(c_0_75, negated_conjecture, (k2_mcart_1(esk2_0)=esk4_0), inference(spm,[status(thm)],[c_0_68, c_0_59])).
% 0.19/0.38  cnf(c_0_76, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_40]), c_0_23]), c_0_42]), c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_77, plain, (r2_hidden(X1,k5_enumset1(X1,X1,X2,X3,X4,X5,X6))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_70])])).
% 0.19/0.38  cnf(c_0_78, negated_conjecture, (~r1_tarski(k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k4_tarski(X1,esk4_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 0.19/0.38  cnf(c_0_79, negated_conjecture, (esk3_0=esk2_0|esk4_0=esk2_0), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.38  cnf(c_0_80, plain, (r1_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X1,X1,X2,X3,X4,X5,X6))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.38  cnf(c_0_81, plain, (k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_82, negated_conjecture, (esk3_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])])).
% 0.19/0.38  cnf(c_0_83, plain, (k2_zfmisc_1(k5_enumset1(X1,X1,X1,X1,X1,X1,X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3))=k5_enumset1(k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X2),k4_tarski(X1,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_40]), c_0_23]), c_0_23]), c_0_23]), c_0_42]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_45])).
% 0.19/0.38  cnf(c_0_84, negated_conjecture, (k4_tarski(esk2_0,esk4_0)=esk2_0), inference(rw,[status(thm)],[c_0_59, c_0_82])).
% 0.19/0.38  cnf(c_0_85, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.38  cnf(c_0_86, negated_conjecture, (k2_zfmisc_1(k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0),k5_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,esk4_0,X1))=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,k4_tarski(esk2_0,X1))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.38  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_80])]), c_0_73]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 88
% 0.19/0.38  # Proof object clause steps            : 49
% 0.19/0.38  # Proof object formula steps           : 39
% 0.19/0.38  # Proof object conjectures             : 15
% 0.19/0.38  # Proof object clause conjectures      : 12
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 23
% 0.19/0.38  # Proof object initial formulas used   : 19
% 0.19/0.38  # Proof object generating inferences   : 10
% 0.19/0.38  # Proof object simplifying inferences  : 113
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 19
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 38
% 0.19/0.38  # Removed in clause preprocessing      : 9
% 0.19/0.38  # Initial clauses in saturation        : 29
% 0.19/0.38  # Processed clauses                    : 89
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 6
% 0.19/0.38  # ...remaining for further processing  : 82
% 0.19/0.38  # Other redundant clauses eliminated   : 14
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 7
% 0.19/0.38  # Generated clauses                    : 128
% 0.19/0.38  # ...of the previous two non-trivial   : 121
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 120
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 14
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 38
% 0.19/0.38  #    Positive orientable unit clauses  : 24
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 5
% 0.19/0.38  #    Non-unit-clauses                  : 9
% 0.19/0.38  # Current number of unprocessed clauses: 76
% 0.19/0.38  # ...number of literals in the above   : 109
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 45
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 49
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 49
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.38  # Unit Clause-clause subsumption calls : 6
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 43
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4080
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.002 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
