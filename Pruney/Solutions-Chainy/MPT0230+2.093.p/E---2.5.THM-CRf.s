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
% DateTime   : Thu Dec  3 10:38:40 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 663 expanded)
%              Number of clauses        :   60 ( 315 expanded)
%              Number of leaves         :   15 ( 170 expanded)
%              Depth                    :   14
%              Number of atoms          :  189 (1218 expanded)
%              Number of equality atoms :  109 ( 836 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t90_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_xboole_1)).

fof(t47_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t25_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(l38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    <=> ( ~ r2_hidden(X1,X3)
        & ( r2_hidden(X2,X3)
          | X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(t96_enumset1,axiom,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).

fof(t93_enumset1,axiom,(
    ! [X1,X2,X3] : k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l53_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t37_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t136_enumset1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != X2
        & X1 != X3
        & k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1)) != k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

fof(c_0_15,plain,(
    ! [X22,X23] : r1_xboole_0(k4_xboole_0(X22,k3_xboole_0(X22,X23)),X23) ),
    inference(variable_rename,[status(thm)],[t90_xboole_1])).

fof(c_0_16,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k3_xboole_0(X20,X21)) = k4_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t47_xboole_1])).

fof(c_0_17,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X2)) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
          & X1 != X2
          & X1 != X3 ) ),
    inference(assume_negation,[status(cth)],[t25_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X45,X46,X47] :
      ( ( ~ r2_hidden(X45,X47)
        | k4_xboole_0(k2_tarski(X45,X46),X47) != k1_tarski(X45) )
      & ( r2_hidden(X46,X47)
        | X45 = X46
        | k4_xboole_0(k2_tarski(X45,X46),X47) != k1_tarski(X45) )
      & ( ~ r2_hidden(X46,X47)
        | r2_hidden(X45,X47)
        | k4_xboole_0(k2_tarski(X45,X46),X47) = k1_tarski(X45) )
      & ( X45 != X46
        | r2_hidden(X45,X47)
        | k4_xboole_0(k2_tarski(X45,X46),X47) = k1_tarski(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).

fof(c_0_23,plain,(
    ! [X44] : k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44) = k1_tarski(X44) ),
    inference(variable_rename,[status(thm)],[t96_enumset1])).

fof(c_0_24,plain,(
    ! [X41,X42,X43] : k6_enumset1(X41,X41,X41,X41,X41,X41,X42,X43) = k1_enumset1(X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t93_enumset1])).

fof(c_0_25,plain,(
    ! [X38,X39,X40] : k2_enumset1(X38,X38,X39,X40) = k1_enumset1(X38,X39,X40) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X31,X32,X33,X34] : k2_enumset1(X31,X32,X33,X34) = k2_xboole_0(k2_tarski(X31,X32),k2_tarski(X33,X34)) ),
    inference(variable_rename,[status(thm)],[l53_enumset1])).

fof(c_0_27,plain,(
    ! [X5,X6] :
      ( ( ~ r1_xboole_0(X5,X6)
        | k3_xboole_0(X5,X6) = k1_xboole_0 )
      & ( k3_xboole_0(X5,X6) != k1_xboole_0
        | r1_xboole_0(X5,X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ( k4_xboole_0(X18,X19) != k1_xboole_0
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | k4_xboole_0(X18,X19) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_32,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))
    & esk3_0 != esk4_0
    & esk3_0 != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X3),X2) != k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( k2_enumset1(X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = X7 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_39,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | k4_xboole_0(k2_tarski(X1,X2),X3) = k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_45,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X24
        | X25 != k1_tarski(X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k1_tarski(X24) )
      & ( ~ r2_hidden(esk2_2(X28,X29),X29)
        | esk2_2(X28,X29) != X28
        | X29 = k1_tarski(X28) )
      & ( r2_hidden(esk2_2(X28,X29),X29)
        | esk2_2(X28,X29) = X28
        | X29 = k1_tarski(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_46,plain,
    ( k4_xboole_0(k2_tarski(X1,X3),X2) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_48,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X3)
    | X1 != X2 ),
    inference(rw,[status(thm)],[c_0_41,c_0_34])).

fof(c_0_51,plain,(
    ! [X35,X36,X37] :
      ( X35 = X36
      | X35 = X37
      | k4_xboole_0(k1_enumset1(X35,X36,X37),k1_tarski(X35)) = k2_tarski(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t136_enumset1])])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_tarski(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) != k2_tarski(X1,X1)
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_49])).

cnf(c_0_57,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_59,plain,
    ( X1 = X2
    | X1 = X3
    | k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1)) = k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_xboole_0
    | ~ r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_tarski(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_53])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[c_0_54,c_0_34])).

cnf(c_0_63,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),k1_xboole_0) != k2_tarski(X1,X1)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( k4_xboole_0(k2_tarski(X1,X1),X2) = k2_tarski(X1,X1)
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,plain,
    ( X1 = X3
    | X1 = X2
    | k4_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k2_tarski(X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_36]),c_0_34]),c_0_37])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X1,X1),X2) != k1_xboole_0
    | ~ r2_hidden(X1,k2_tarski(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(k2_tarski(esk3_0,esk3_0),k2_tarski(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_61,c_0_58])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).

cnf(c_0_69,plain,
    ( k4_xboole_0(k2_tarski(X1,X2),X3) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | ~ r2_hidden(X1,k3_xboole_0(k2_tarski(X1,X2),X3)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_19])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,plain,
    ( k4_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X1,X1)) = k2_tarski(X2,X3)
    | X1 = X2
    | X1 = X3 ),
    inference(rw,[status(thm)],[c_0_65,c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_0,k2_tarski(esk4_0,esk5_0))
    | ~ r2_hidden(esk3_0,k2_tarski(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_47]),c_0_48])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(k2_tarski(X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_57])).

cnf(c_0_75,plain,
    ( X1 = X2
    | X1 = X3
    | r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk3_0,k2_tarski(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_78,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_79,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_80,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_49])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77]),c_0_78])).

cnf(c_0_82,plain,
    ( X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_79,c_0_34])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk3_0,k4_xboole_0(X1,k2_tarski(esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( k2_tarski(esk3_0,esk3_0) != k1_xboole_0
    | ~ r2_hidden(esk3_0,k2_tarski(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_67])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = X1
    | esk3_0 = X2
    | r2_hidden(esk3_0,k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_71])).

cnf(c_0_87,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_47]),c_0_48])).

cnf(c_0_88,negated_conjecture,
    ( k2_tarski(esk3_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_76])])).

cnf(c_0_89,negated_conjecture,
    ( esk3_0 = X1 ),
    inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_86]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_89]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:36:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.40  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.18/0.40  # and selection function SelectNegativeLiterals.
% 0.18/0.40  #
% 0.18/0.40  # Preprocessing time       : 0.027 s
% 0.18/0.40  # Presaturation interreduction done
% 0.18/0.40  
% 0.18/0.40  # Proof found!
% 0.18/0.40  # SZS status Theorem
% 0.18/0.40  # SZS output start CNFRefutation
% 0.18/0.40  fof(t90_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_xboole_1)).
% 0.18/0.40  fof(t47_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 0.18/0.40  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.18/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.40  fof(t25_zfmisc_1, conjecture, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 0.18/0.40  fof(l38_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)<=>(~(r2_hidden(X1,X3))&(r2_hidden(X2,X3)|X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 0.18/0.40  fof(t96_enumset1, axiom, ![X1]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_enumset1)).
% 0.18/0.40  fof(t93_enumset1, axiom, ![X1, X2, X3]:k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_enumset1)).
% 0.18/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.40  fof(l53_enumset1, axiom, ![X1, X2, X3, X4]:k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 0.18/0.40  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.18/0.40  fof(t37_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 0.18/0.40  fof(idempotence_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 0.18/0.40  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.40  fof(t136_enumset1, axiom, ![X1, X2, X3]:~(((X1!=X2&X1!=X3)&k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1))!=k2_tarski(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 0.18/0.40  fof(c_0_15, plain, ![X22, X23]:r1_xboole_0(k4_xboole_0(X22,k3_xboole_0(X22,X23)),X23), inference(variable_rename,[status(thm)],[t90_xboole_1])).
% 0.18/0.40  fof(c_0_16, plain, ![X20, X21]:k4_xboole_0(X20,k3_xboole_0(X20,X21))=k4_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t47_xboole_1])).
% 0.18/0.40  fof(c_0_17, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.18/0.40  cnf(c_0_18, plain, (r1_xboole_0(k4_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.40  cnf(c_0_19, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X2))=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.40  fof(c_0_20, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.40  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3))), inference(assume_negation,[status(cth)],[t25_zfmisc_1])).
% 0.18/0.40  fof(c_0_22, plain, ![X45, X46, X47]:(((~r2_hidden(X45,X47)|k4_xboole_0(k2_tarski(X45,X46),X47)!=k1_tarski(X45))&(r2_hidden(X46,X47)|X45=X46|k4_xboole_0(k2_tarski(X45,X46),X47)!=k1_tarski(X45)))&((~r2_hidden(X46,X47)|r2_hidden(X45,X47)|k4_xboole_0(k2_tarski(X45,X46),X47)=k1_tarski(X45))&(X45!=X46|r2_hidden(X45,X47)|k4_xboole_0(k2_tarski(X45,X46),X47)=k1_tarski(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l38_zfmisc_1])])])])).
% 0.18/0.40  fof(c_0_23, plain, ![X44]:k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44)=k1_tarski(X44), inference(variable_rename,[status(thm)],[t96_enumset1])).
% 0.18/0.40  fof(c_0_24, plain, ![X41, X42, X43]:k6_enumset1(X41,X41,X41,X41,X41,X41,X42,X43)=k1_enumset1(X41,X42,X43), inference(variable_rename,[status(thm)],[t93_enumset1])).
% 0.18/0.40  fof(c_0_25, plain, ![X38, X39, X40]:k2_enumset1(X38,X38,X39,X40)=k1_enumset1(X38,X39,X40), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.40  fof(c_0_26, plain, ![X31, X32, X33, X34]:k2_enumset1(X31,X32,X33,X34)=k2_xboole_0(k2_tarski(X31,X32),k2_tarski(X33,X34)), inference(variable_rename,[status(thm)],[l53_enumset1])).
% 0.18/0.40  fof(c_0_27, plain, ![X5, X6]:((~r1_xboole_0(X5,X6)|k3_xboole_0(X5,X6)=k1_xboole_0)&(k3_xboole_0(X5,X6)!=k1_xboole_0|r1_xboole_0(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.18/0.40  cnf(c_0_28, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.40  cnf(c_0_29, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.18/0.40  fof(c_0_30, plain, ![X18, X19]:((k4_xboole_0(X18,X19)!=k1_xboole_0|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|k4_xboole_0(X18,X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_xboole_1])])).
% 0.18/0.40  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.40  fof(c_0_32, negated_conjecture, ((r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))&esk3_0!=esk4_0)&esk3_0!=esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.18/0.40  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X1,X3),X2)!=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_34, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.40  cnf(c_0_35, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.40  cnf(c_0_36, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.40  cnf(c_0_37, plain, (k2_enumset1(X1,X2,X3,X4)=k2_xboole_0(k2_tarski(X1,X2),k2_tarski(X3,X4))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.40  fof(c_0_38, plain, ![X7]:k2_xboole_0(X7,X7)=X7, inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).
% 0.18/0.40  cnf(c_0_39, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.40  cnf(c_0_40, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.40  cnf(c_0_41, plain, (r2_hidden(X1,X3)|k4_xboole_0(k2_tarski(X1,X2),X3)=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_42, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.40  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.18/0.40  cnf(c_0_44, negated_conjecture, (r1_tarski(k1_tarski(esk3_0),k2_tarski(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  fof(c_0_45, plain, ![X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X26,X25)|X26=X24|X25!=k1_tarski(X24))&(X27!=X24|r2_hidden(X27,X25)|X25!=k1_tarski(X24)))&((~r2_hidden(esk2_2(X28,X29),X29)|esk2_2(X28,X29)!=X28|X29=k1_tarski(X28))&(r2_hidden(esk2_2(X28,X29),X29)|esk2_2(X28,X29)=X28|X29=k1_tarski(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.40  cnf(c_0_46, plain, (k4_xboole_0(k2_tarski(X1,X3),X2)!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.18/0.40  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.18/0.40  cnf(c_0_48, plain, (k2_xboole_0(X1,X1)=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.40  cnf(c_0_49, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.18/0.40  cnf(c_0_50, plain, (k4_xboole_0(k2_tarski(X1,X2),X3)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X3)|X1!=X2), inference(rw,[status(thm)],[c_0_41, c_0_34])).
% 0.18/0.40  fof(c_0_51, plain, ![X35, X36, X37]:(X35=X36|X35=X37|k4_xboole_0(k1_enumset1(X35,X36,X37),k1_tarski(X35))=k2_tarski(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t136_enumset1])])).
% 0.18/0.40  cnf(c_0_52, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.40  cnf(c_0_53, negated_conjecture, (r1_tarski(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_tarski(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_44, c_0_34])).
% 0.18/0.40  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.40  cnf(c_0_55, plain, (k4_xboole_0(k2_tarski(X1,X2),X3)!=k2_tarski(X1,X1)|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.18/0.40  cnf(c_0_56, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X1))=k4_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_49])).
% 0.18/0.40  cnf(c_0_57, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_50])).
% 0.18/0.40  cnf(c_0_58, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_48, c_0_47])).
% 0.18/0.40  cnf(c_0_59, plain, (X1=X2|X1=X3|k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X1))=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.40  cnf(c_0_60, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)!=k1_xboole_0|~r2_hidden(X1,k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_46, c_0_52])).
% 0.18/0.40  cnf(c_0_61, negated_conjecture, (k4_xboole_0(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),k2_tarski(esk4_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_53])).
% 0.18/0.40  cnf(c_0_62, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[c_0_54, c_0_34])).
% 0.18/0.40  cnf(c_0_63, plain, (k4_xboole_0(k2_tarski(X1,X2),k1_xboole_0)!=k2_tarski(X1,X1)|~r2_hidden(X1,k4_xboole_0(X3,k2_tarski(X1,X2)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.18/0.40  cnf(c_0_64, plain, (k4_xboole_0(k2_tarski(X1,X1),X2)=k2_tarski(X1,X1)|r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_57, c_0_58])).
% 0.18/0.40  cnf(c_0_65, plain, (X1=X3|X1=X2|k4_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=k2_tarski(X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_36]), c_0_34]), c_0_37])).
% 0.18/0.40  cnf(c_0_66, plain, (r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X1,X1),X2)!=k1_xboole_0|~r2_hidden(X1,k2_tarski(X1,X3))), inference(spm,[status(thm)],[c_0_60, c_0_57])).
% 0.18/0.40  cnf(c_0_67, negated_conjecture, (k4_xboole_0(k2_tarski(esk3_0,esk3_0),k2_tarski(esk4_0,esk5_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_61, c_0_58])).
% 0.18/0.40  cnf(c_0_68, plain, (r2_hidden(X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_62])])).
% 0.18/0.40  cnf(c_0_69, plain, (k4_xboole_0(k2_tarski(X1,X2),X3)!=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|~r2_hidden(X1,k3_xboole_0(k2_tarski(X1,X2),X3))), inference(spm,[status(thm)],[c_0_46, c_0_19])).
% 0.18/0.40  cnf(c_0_70, plain, (r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.18/0.40  cnf(c_0_71, plain, (k4_xboole_0(k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X3)),k2_tarski(X1,X1))=k2_tarski(X2,X3)|X1=X2|X1=X3), inference(rw,[status(thm)],[c_0_65, c_0_58])).
% 0.18/0.40  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_0,k2_tarski(esk4_0,esk5_0))|~r2_hidden(esk3_0,k2_tarski(esk3_0,X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.40  cnf(c_0_73, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_47]), c_0_48])).
% 0.18/0.40  cnf(c_0_74, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(k2_tarski(X1,X1),X2))), inference(spm,[status(thm)],[c_0_69, c_0_57])).
% 0.18/0.40  cnf(c_0_75, plain, (X1=X2|X1=X3|r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,k2_tarski(X3,X2))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.40  cnf(c_0_76, negated_conjecture, (r2_hidden(esk3_0,k2_tarski(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.18/0.40  cnf(c_0_77, negated_conjecture, (esk3_0!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_78, negated_conjecture, (esk3_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_79, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.40  cnf(c_0_80, plain, (r2_hidden(X1,k4_xboole_0(X2,k2_tarski(X1,X1)))|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_49])).
% 0.18/0.40  cnf(c_0_81, negated_conjecture, (r2_hidden(esk3_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77]), c_0_78])).
% 0.18/0.40  cnf(c_0_82, plain, (X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_79, c_0_34])).
% 0.18/0.40  cnf(c_0_83, negated_conjecture, (r2_hidden(esk3_0,k4_xboole_0(X1,k2_tarski(esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.18/0.40  cnf(c_0_84, plain, (X1=X2|~r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_82])).
% 0.18/0.40  cnf(c_0_85, negated_conjecture, (k2_tarski(esk3_0,esk3_0)!=k1_xboole_0|~r2_hidden(esk3_0,k2_tarski(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_55, c_0_67])).
% 0.18/0.40  cnf(c_0_86, negated_conjecture, (esk3_0=X1|esk3_0=X2|r2_hidden(esk3_0,k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_83, c_0_71])).
% 0.18/0.40  cnf(c_0_87, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_47]), c_0_48])).
% 0.18/0.40  cnf(c_0_88, negated_conjecture, (k2_tarski(esk3_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_76])])).
% 0.18/0.40  cnf(c_0_89, negated_conjecture, (esk3_0=X1), inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_86]), c_0_87])).
% 0.18/0.40  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_89]), c_0_89]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 91
% 0.18/0.40  # Proof object clause steps            : 60
% 0.18/0.40  # Proof object formula steps           : 31
% 0.18/0.40  # Proof object conjectures             : 18
% 0.18/0.40  # Proof object clause conjectures      : 15
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 19
% 0.18/0.40  # Proof object initial formulas used   : 15
% 0.18/0.40  # Proof object generating inferences   : 24
% 0.18/0.40  # Proof object simplifying inferences  : 29
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 17
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 31
% 0.18/0.40  # Removed in clause preprocessing      : 3
% 0.18/0.40  # Initial clauses in saturation        : 28
% 0.18/0.40  # Processed clauses                    : 283
% 0.18/0.40  # ...of these trivial                  : 9
% 0.18/0.40  # ...subsumed                          : 90
% 0.18/0.40  # ...remaining for further processing  : 184
% 0.18/0.40  # Other redundant clauses eliminated   : 38
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 1
% 0.18/0.40  # Backward-rewritten                   : 142
% 0.18/0.40  # Generated clauses                    : 2387
% 0.18/0.40  # ...of the previous two non-trivial   : 1931
% 0.18/0.40  # Contextual simplify-reflections      : 1
% 0.18/0.40  # Paramodulations                      : 2340
% 0.18/0.40  # Factorizations                       : 8
% 0.18/0.40  # Equation resolutions                 : 40
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
% 0.18/0.40  # Current number of processed clauses  : 9
% 0.18/0.40  #    Positive orientable unit clauses  : 5
% 0.18/0.40  #    Positive unorientable unit clauses: 1
% 0.18/0.40  #    Negative unit clauses             : 0
% 0.18/0.40  #    Non-unit-clauses                  : 3
% 0.18/0.40  # Current number of unprocessed clauses: 1643
% 0.18/0.40  # ...number of literals in the above   : 5773
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 173
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 1337
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 1112
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 84
% 0.18/0.40  # Unit Clause-clause subsumption calls : 85
% 0.18/0.40  # Rewrite failures with RHS unbound    : 5
% 0.18/0.40  # BW rewrite match attempts            : 127
% 0.18/0.40  # BW rewrite match successes           : 111
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 40168
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.062 s
% 0.18/0.40  # System time              : 0.005 s
% 0.18/0.40  # Total time               : 0.067 s
% 0.18/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
