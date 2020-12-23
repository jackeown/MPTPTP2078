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
% DateTime   : Thu Dec  3 10:47:12 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 290 expanded)
%              Number of clauses        :   43 ( 124 expanded)
%              Number of leaves         :   12 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 ( 578 expanded)
%              Number of equality atoms :   93 ( 388 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X23
        | X26 = X24
        | X25 != k2_tarski(X23,X24) )
      & ( X27 != X23
        | r2_hidden(X27,X25)
        | X25 != k2_tarski(X23,X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k2_tarski(X23,X24) )
      & ( esk3_3(X28,X29,X30) != X28
        | ~ r2_hidden(esk3_3(X28,X29,X30),X30)
        | X30 = k2_tarski(X28,X29) )
      & ( esk3_3(X28,X29,X30) != X29
        | ~ r2_hidden(esk3_3(X28,X29,X30),X30)
        | X30 = k2_tarski(X28,X29) )
      & ( r2_hidden(esk3_3(X28,X29,X30),X30)
        | esk3_3(X28,X29,X30) = X28
        | esk3_3(X28,X29,X30) = X29
        | X30 = k2_tarski(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X33,X34] : k1_enumset1(X33,X33,X34) = k2_tarski(X33,X34) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X35,X36,X37] : k2_enumset1(X35,X35,X36,X37) = k1_enumset1(X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

fof(c_0_16,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(X40,X41)
        | ~ r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))) )
      & ( X40 != X42
        | ~ r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))) )
      & ( ~ r2_hidden(X40,X41)
        | X40 = X42
        | r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_17,plain,(
    ! [X32] : k2_tarski(X32,X32) = k1_tarski(X32) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X20,X21] :
      ( ( r1_tarski(X20,X21)
        | X20 != X21 )
      & ( r1_tarski(X21,X20)
        | X20 != X21 )
      & ( ~ r1_tarski(X20,X21)
        | ~ r1_tarski(X21,X20)
        | X20 = X21 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_22,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_23,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

fof(c_0_26,plain,(
    ! [X46,X47,X48] :
      ( ~ r2_hidden(X46,X47)
      | ~ r1_tarski(X46,X48)
      | r1_tarski(k1_setfam_1(X47),X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_19]),c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).

fof(c_0_31,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k4_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k4_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_24]),c_0_19]),c_0_20])).

cnf(c_0_35,plain,
    ( X1 = X2
    | r2_hidden(X1,k4_xboole_0(k2_enumset1(X1,X1,X1,X3),k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_37,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),k2_enumset1(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35])])).

fof(c_0_41,plain,(
    ! [X38,X39] :
      ( ( k4_xboole_0(k1_tarski(X38),k1_tarski(X39)) != k1_tarski(X38)
        | X38 != X39 )
      & ( X38 = X39
        | k4_xboole_0(k1_tarski(X38),k1_tarski(X39)) = k1_tarski(X38) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_19]),c_0_20])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),k2_enumset1(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X43,X44] :
      ( ( r2_hidden(esk4_2(X43,X44),X43)
        | X43 = k1_xboole_0
        | r1_tarski(X44,k1_setfam_1(X43)) )
      & ( ~ r1_tarski(X44,esk4_2(X43,X44))
        | X43 = k1_xboole_0
        | r1_tarski(X44,k1_setfam_1(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).

cnf(c_0_51,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( k1_setfam_1(k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),k2_enumset1(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))) = esk5_0
    | ~ r1_tarski(esk5_0,k1_setfam_1(k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),k2_enumset1(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( X1 = X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_24]),c_0_24]),c_0_24]),c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_54,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_56,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_19]),c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_34])).

cnf(c_0_58,plain,
    ( r2_hidden(esk4_2(k2_enumset1(X1,X1,X1,X2),X3),k2_enumset1(X1,X1,X1,X2))
    | r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_54]),c_0_55])).

cnf(c_0_59,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_60,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( X1 != X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_24]),c_0_24]),c_0_24]),c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_63,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk4_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_33])]),c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_43])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 4.18/4.36  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 4.18/4.36  # and selection function SelectNegativeLiterals.
% 4.18/4.36  #
% 4.18/4.36  # Preprocessing time       : 0.029 s
% 4.18/4.36  # Presaturation interreduction done
% 4.18/4.36  
% 4.18/4.36  # Proof found!
% 4.18/4.36  # SZS status Theorem
% 4.18/4.36  # SZS output start CNFRefutation
% 4.18/4.36  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 4.18/4.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.18/4.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.18/4.36  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.18/4.36  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.18/4.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.18/4.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.18/4.36  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 4.18/4.36  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.18/4.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.18/4.36  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 4.18/4.36  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 4.18/4.36  fof(c_0_12, plain, ![X23, X24, X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X26,X25)|(X26=X23|X26=X24)|X25!=k2_tarski(X23,X24))&((X27!=X23|r2_hidden(X27,X25)|X25!=k2_tarski(X23,X24))&(X27!=X24|r2_hidden(X27,X25)|X25!=k2_tarski(X23,X24))))&(((esk3_3(X28,X29,X30)!=X28|~r2_hidden(esk3_3(X28,X29,X30),X30)|X30=k2_tarski(X28,X29))&(esk3_3(X28,X29,X30)!=X29|~r2_hidden(esk3_3(X28,X29,X30),X30)|X30=k2_tarski(X28,X29)))&(r2_hidden(esk3_3(X28,X29,X30),X30)|(esk3_3(X28,X29,X30)=X28|esk3_3(X28,X29,X30)=X29)|X30=k2_tarski(X28,X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 4.18/4.36  fof(c_0_13, plain, ![X33, X34]:k1_enumset1(X33,X33,X34)=k2_tarski(X33,X34), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 4.18/4.36  fof(c_0_14, plain, ![X35, X36, X37]:k2_enumset1(X35,X35,X36,X37)=k1_enumset1(X35,X36,X37), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 4.18/4.36  fof(c_0_15, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 4.18/4.36  fof(c_0_16, plain, ![X40, X41, X42]:(((r2_hidden(X40,X41)|~r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))))&(X40!=X42|~r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42)))))&(~r2_hidden(X40,X41)|X40=X42|r2_hidden(X40,k4_xboole_0(X41,k1_tarski(X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 4.18/4.36  fof(c_0_17, plain, ![X32]:k2_tarski(X32,X32)=k1_tarski(X32), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 4.18/4.36  cnf(c_0_18, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.18/4.36  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 4.18/4.36  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.18/4.36  fof(c_0_21, plain, ![X20, X21]:(((r1_tarski(X20,X21)|X20!=X21)&(r1_tarski(X21,X20)|X20!=X21))&(~r1_tarski(X20,X21)|~r1_tarski(X21,X20)|X20=X21)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.18/4.36  fof(c_0_22, negated_conjecture, k1_setfam_1(k1_tarski(esk5_0))!=esk5_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 4.18/4.36  cnf(c_0_23, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.18/4.36  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.18/4.36  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 4.18/4.36  fof(c_0_26, plain, ![X46, X47, X48]:(~r2_hidden(X46,X47)|~r1_tarski(X46,X48)|r1_tarski(k1_setfam_1(X47),X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 4.18/4.36  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.18/4.36  cnf(c_0_28, negated_conjecture, (k1_setfam_1(k1_tarski(esk5_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.18/4.36  cnf(c_0_29, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_19]), c_0_20])).
% 4.18/4.36  cnf(c_0_30, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_25])])).
% 4.18/4.36  fof(c_0_31, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k4_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k4_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k4_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))&(~r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k4_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 4.18/4.36  cnf(c_0_32, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.18/4.36  cnf(c_0_33, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 4.18/4.36  cnf(c_0_34, negated_conjecture, (k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_24]), c_0_19]), c_0_20])).
% 4.18/4.36  cnf(c_0_35, plain, (X1=X2|r2_hidden(X1,k4_xboole_0(k2_enumset1(X1,X1,X1,X3),k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 4.18/4.36  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 4.18/4.36  fof(c_0_37, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 4.18/4.36  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.18/4.36  cnf(c_0_39, plain, (r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 4.18/4.36  cnf(c_0_40, negated_conjecture, (r2_hidden(esk5_0,k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),k2_enumset1(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35])])).
% 4.18/4.36  fof(c_0_41, plain, ![X38, X39]:((k4_xboole_0(k1_tarski(X38),k1_tarski(X39))!=k1_tarski(X38)|X38!=X39)&(X38=X39|k4_xboole_0(k1_tarski(X38),k1_tarski(X39))=k1_tarski(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 4.18/4.36  cnf(c_0_42, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_36])).
% 4.18/4.36  cnf(c_0_43, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 4.18/4.36  cnf(c_0_44, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_19]), c_0_20])).
% 4.18/4.36  cnf(c_0_45, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.18/4.36  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_setfam_1(k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),k2_enumset1(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))),esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 4.18/4.36  cnf(c_0_47, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.18/4.36  fof(c_0_48, plain, ![X43, X44]:((r2_hidden(esk4_2(X43,X44),X43)|(X43=k1_xboole_0|r1_tarski(X44,k1_setfam_1(X43))))&(~r1_tarski(X44,esk4_2(X43,X44))|(X43=k1_xboole_0|r1_tarski(X44,k1_setfam_1(X43))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 4.18/4.36  cnf(c_0_49, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 4.18/4.36  cnf(c_0_50, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_44])])).
% 4.18/4.36  cnf(c_0_51, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 4.18/4.36  cnf(c_0_52, negated_conjecture, (k1_setfam_1(k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),k2_enumset1(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))))=esk5_0|~r1_tarski(esk5_0,k1_setfam_1(k4_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,X1),k2_enumset1(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 4.18/4.36  cnf(c_0_53, plain, (X1=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_24]), c_0_24]), c_0_24]), c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 4.18/4.36  cnf(c_0_54, plain, (r2_hidden(esk4_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.18/4.36  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 4.18/4.36  cnf(c_0_56, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_19]), c_0_20])).
% 4.18/4.36  cnf(c_0_57, negated_conjecture, (~r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_34])).
% 4.18/4.36  cnf(c_0_58, plain, (r2_hidden(esk4_2(k2_enumset1(X1,X1,X1,X2),X3),k2_enumset1(X1,X1,X1,X2))|r1_tarski(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_54]), c_0_55])).
% 4.18/4.36  cnf(c_0_59, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.18/4.36  cnf(c_0_60, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_56])).
% 4.18/4.36  cnf(c_0_61, negated_conjecture, (r2_hidden(esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 4.18/4.36  cnf(c_0_62, plain, (X1!=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))!=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_24]), c_0_24]), c_0_24]), c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 4.18/4.36  cnf(c_0_63, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk4_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.18/4.36  cnf(c_0_64, negated_conjecture, (esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0)=esk5_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 4.18/4.36  cnf(c_0_65, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))!=k2_enumset1(X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_62])).
% 4.18/4.36  cnf(c_0_66, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_33])]), c_0_57])).
% 4.18/4.36  cnf(c_0_67, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_43])]), ['proof']).
% 4.18/4.36  # SZS output end CNFRefutation
% 4.18/4.36  # Proof object total steps             : 68
% 4.18/4.36  # Proof object clause steps            : 43
% 4.18/4.36  # Proof object formula steps           : 25
% 4.18/4.36  # Proof object conjectures             : 13
% 4.18/4.36  # Proof object clause conjectures      : 10
% 4.18/4.36  # Proof object formula conjectures     : 3
% 4.18/4.36  # Proof object initial clauses used    : 17
% 4.18/4.36  # Proof object initial formulas used   : 12
% 4.18/4.36  # Proof object generating inferences   : 13
% 4.18/4.36  # Proof object simplifying inferences  : 46
% 4.18/4.36  # Training examples: 0 positive, 0 negative
% 4.18/4.36  # Parsed axioms                        : 13
% 4.18/4.36  # Removed by relevancy pruning/SinE    : 0
% 4.18/4.36  # Initial clauses                      : 31
% 4.18/4.36  # Removed in clause preprocessing      : 3
% 4.18/4.36  # Initial clauses in saturation        : 28
% 4.18/4.36  # Processed clauses                    : 5648
% 4.18/4.36  # ...of these trivial                  : 84
% 4.18/4.36  # ...subsumed                          : 3807
% 4.18/4.36  # ...remaining for further processing  : 1757
% 4.18/4.36  # Other redundant clauses eliminated   : 6207
% 4.18/4.36  # Clauses deleted for lack of memory   : 0
% 4.18/4.36  # Backward-subsumed                    : 38
% 4.18/4.36  # Backward-rewritten                   : 399
% 4.18/4.36  # Generated clauses                    : 546111
% 4.18/4.36  # ...of the previous two non-trivial   : 509900
% 4.18/4.36  # Contextual simplify-reflections      : 16
% 4.18/4.36  # Paramodulations                      : 539761
% 4.18/4.36  # Factorizations                       : 144
% 4.18/4.36  # Equation resolutions                 : 6208
% 4.18/4.36  # Propositional unsat checks           : 0
% 4.18/4.36  #    Propositional check models        : 0
% 4.18/4.36  #    Propositional check unsatisfiable : 0
% 4.18/4.36  #    Propositional clauses             : 0
% 4.18/4.36  #    Propositional clauses after purity: 0
% 4.18/4.36  #    Propositional unsat core size     : 0
% 4.18/4.36  #    Propositional preprocessing time  : 0.000
% 4.18/4.36  #    Propositional encoding time       : 0.000
% 4.18/4.36  #    Propositional solver time         : 0.000
% 4.18/4.36  #    Success case prop preproc time    : 0.000
% 4.18/4.36  #    Success case prop encoding time   : 0.000
% 4.18/4.36  #    Success case prop solver time     : 0.000
% 4.18/4.36  # Current number of processed clauses  : 1284
% 4.18/4.36  #    Positive orientable unit clauses  : 51
% 4.18/4.36  #    Positive unorientable unit clauses: 0
% 4.18/4.36  #    Negative unit clauses             : 4
% 4.18/4.36  #    Non-unit-clauses                  : 1229
% 4.18/4.36  # Current number of unprocessed clauses: 503446
% 4.18/4.36  # ...number of literals in the above   : 2486880
% 4.18/4.36  # Current number of archived formulas  : 0
% 4.18/4.36  # Current number of archived clauses   : 466
% 4.18/4.36  # Clause-clause subsumption calls (NU) : 156507
% 4.18/4.36  # Rec. Clause-clause subsumption calls : 78208
% 4.18/4.36  # Non-unit clause-clause subsumptions  : 3515
% 4.18/4.36  # Unit Clause-clause subsumption calls : 3174
% 4.18/4.36  # Rewrite failures with RHS unbound    : 0
% 4.18/4.36  # BW rewrite match attempts            : 155
% 4.18/4.36  # BW rewrite match successes           : 17
% 4.18/4.36  # Condensation attempts                : 0
% 4.18/4.36  # Condensation successes               : 0
% 4.18/4.36  # Termbank termtop insertions          : 12544907
% 4.18/4.38  
% 4.18/4.38  # -------------------------------------------------
% 4.18/4.38  # User time                : 3.851 s
% 4.18/4.38  # System time              : 0.186 s
% 4.18/4.38  # Total time               : 4.038 s
% 4.18/4.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
