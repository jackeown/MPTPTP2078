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
% DateTime   : Thu Dec  3 10:47:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 453 expanded)
%              Number of clauses        :   50 ( 197 expanded)
%              Number of leaves         :   11 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 ( 980 expanded)
%              Number of equality atoms :  121 ( 565 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X13
        | X16 = X14
        | X15 != k2_tarski(X13,X14) )
      & ( X17 != X13
        | r2_hidden(X17,X15)
        | X15 != k2_tarski(X13,X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k2_tarski(X13,X14) )
      & ( esk2_3(X18,X19,X20) != X18
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_tarski(X18,X19) )
      & ( esk2_3(X18,X19,X20) != X19
        | ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k2_tarski(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X20)
        | esk2_3(X18,X19,X20) = X18
        | esk2_3(X18,X19,X20) = X19
        | X20 = k2_tarski(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X23,X24] : k1_enumset1(X23,X23,X24) = k2_tarski(X23,X24) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X25,X26,X27] : k2_enumset1(X25,X25,X26,X27) = k1_enumset1(X25,X26,X27) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(X32,X33)
        | ~ r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))) )
      & ( X32 != X34
        | ~ r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))) )
      & ( ~ r2_hidden(X32,X33)
        | X32 = X34
        | r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X28,X29] :
      ( ( ~ r1_tarski(X28,k1_tarski(X29))
        | X28 = k1_xboole_0
        | X28 = k1_tarski(X29) )
      & ( X28 != k1_xboole_0
        | r1_tarski(X28,k1_tarski(X29)) )
      & ( X28 != k1_tarski(X29)
        | r1_tarski(X28,k1_tarski(X29)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X30,X31] :
      ( ( k4_xboole_0(k1_tarski(X30),k1_tarski(X31)) != k1_tarski(X30)
        | X30 != X31 )
      & ( X30 = X31
        | k4_xboole_0(k1_tarski(X30),k1_tarski(X31)) = k1_tarski(X30) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

fof(c_0_23,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_26,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_18]),c_0_19])).

cnf(c_0_27,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_18]),c_0_19])).

fof(c_0_30,plain,(
    ! [X35,X36,X37,X38,X39,X41,X44,X45,X46,X47] :
      ( ( ~ r2_hidden(X37,X36)
        | ~ r2_hidden(X38,X35)
        | r2_hidden(X37,X38)
        | X36 != k1_setfam_1(X35)
        | X35 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X35,X36,X39),X35)
        | r2_hidden(X39,X36)
        | X36 != k1_setfam_1(X35)
        | X35 = k1_xboole_0 )
      & ( ~ r2_hidden(X39,esk3_3(X35,X36,X39))
        | r2_hidden(X39,X36)
        | X36 != k1_setfam_1(X35)
        | X35 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X35,X41),X35)
        | ~ r2_hidden(esk4_2(X35,X41),X41)
        | X41 = k1_setfam_1(X35)
        | X35 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X35,X41),esk5_2(X35,X41))
        | ~ r2_hidden(esk4_2(X35,X41),X41)
        | X41 = k1_setfam_1(X35)
        | X35 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X35,X41),X41)
        | ~ r2_hidden(X44,X35)
        | r2_hidden(esk4_2(X35,X41),X44)
        | X41 = k1_setfam_1(X35)
        | X35 = k1_xboole_0 )
      & ( X46 != k1_setfam_1(X45)
        | X46 = k1_xboole_0
        | X45 != k1_xboole_0 )
      & ( X47 != k1_xboole_0
        | X47 = k1_setfam_1(X45)
        | X45 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X1,X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_21]),c_0_21]),c_0_21]),c_0_18]),c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_19])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | X3 != k1_xboole_0
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_enumset1(X3,X3,X3,X3))
    | r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | r2_hidden(X3,X1)
    | X4 != k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(X3,X4) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk3_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( esk3_3(k2_enumset1(X1,X1,X1,X1),X2,X3) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r2_hidden(X3,X2)
    | X2 != k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_45,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk6_0)) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).

cnf(c_0_46,plain,
    ( X1 = esk1_2(X2,X3)
    | r1_tarski(X2,X3)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_41])).

cnf(c_0_47,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | r2_hidden(X3,X1)
    | ~ r2_hidden(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r2_hidden(X2,X3)
    | X3 != k1_setfam_1(k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk6_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_50,plain,
    ( X1 = X2
    | r1_tarski(X3,X4)
    | X3 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_46])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_52,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3),X1)
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_55,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | ~ r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_21]),c_0_18]),c_0_19])).

cnf(c_0_57,plain,
    ( X1 = X2
    | r1_tarski(k1_xboole_0,X3) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_21]),c_0_18]),c_0_19])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | ~ r2_hidden(esk1_2(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_57])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)
    | r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_58,c_0_35])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | k2_enumset1(X1,X1,X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_35])).

cnf(c_0_66,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_62])).

cnf(c_0_67,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_63])).

cnf(c_0_68,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k4_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.20/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.023 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.42  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.20/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.42  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.20/0.42  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.20/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.42  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.20/0.42  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.20/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.42  fof(c_0_11, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X16,X15)|(X16=X13|X16=X14)|X15!=k2_tarski(X13,X14))&((X17!=X13|r2_hidden(X17,X15)|X15!=k2_tarski(X13,X14))&(X17!=X14|r2_hidden(X17,X15)|X15!=k2_tarski(X13,X14))))&(((esk2_3(X18,X19,X20)!=X18|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_tarski(X18,X19))&(esk2_3(X18,X19,X20)!=X19|~r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k2_tarski(X18,X19)))&(r2_hidden(esk2_3(X18,X19,X20),X20)|(esk2_3(X18,X19,X20)=X18|esk2_3(X18,X19,X20)=X19)|X20=k2_tarski(X18,X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.42  fof(c_0_12, plain, ![X23, X24]:k1_enumset1(X23,X23,X24)=k2_tarski(X23,X24), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.42  fof(c_0_13, plain, ![X25, X26, X27]:k2_enumset1(X25,X25,X26,X27)=k1_enumset1(X25,X26,X27), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.42  fof(c_0_14, plain, ![X32, X33, X34]:(((r2_hidden(X32,X33)|~r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))))&(X32!=X34|~r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34)))))&(~r2_hidden(X32,X33)|X32=X34|r2_hidden(X32,k4_xboole_0(X33,k1_tarski(X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.20/0.42  fof(c_0_15, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.42  fof(c_0_16, plain, ![X28, X29]:((~r1_tarski(X28,k1_tarski(X29))|(X28=k1_xboole_0|X28=k1_tarski(X29)))&((X28!=k1_xboole_0|r1_tarski(X28,k1_tarski(X29)))&(X28!=k1_tarski(X29)|r1_tarski(X28,k1_tarski(X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.20/0.42  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_20, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  fof(c_0_22, plain, ![X30, X31]:((k4_xboole_0(k1_tarski(X30),k1_tarski(X31))!=k1_tarski(X30)|X30!=X31)&(X30=X31|k4_xboole_0(k1_tarski(X30),k1_tarski(X31))=k1_tarski(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.20/0.42  fof(c_0_23, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.42  cnf(c_0_24, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.20/0.42  cnf(c_0_26, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_18]), c_0_19])).
% 0.20/0.42  cnf(c_0_27, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.42  cnf(c_0_28, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_29, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_18]), c_0_19])).
% 0.20/0.42  fof(c_0_30, plain, ![X35, X36, X37, X38, X39, X41, X44, X45, X46, X47]:((((~r2_hidden(X37,X36)|(~r2_hidden(X38,X35)|r2_hidden(X37,X38))|X36!=k1_setfam_1(X35)|X35=k1_xboole_0)&((r2_hidden(esk3_3(X35,X36,X39),X35)|r2_hidden(X39,X36)|X36!=k1_setfam_1(X35)|X35=k1_xboole_0)&(~r2_hidden(X39,esk3_3(X35,X36,X39))|r2_hidden(X39,X36)|X36!=k1_setfam_1(X35)|X35=k1_xboole_0)))&(((r2_hidden(esk5_2(X35,X41),X35)|~r2_hidden(esk4_2(X35,X41),X41)|X41=k1_setfam_1(X35)|X35=k1_xboole_0)&(~r2_hidden(esk4_2(X35,X41),esk5_2(X35,X41))|~r2_hidden(esk4_2(X35,X41),X41)|X41=k1_setfam_1(X35)|X35=k1_xboole_0))&(r2_hidden(esk4_2(X35,X41),X41)|(~r2_hidden(X44,X35)|r2_hidden(esk4_2(X35,X41),X44))|X41=k1_setfam_1(X35)|X35=k1_xboole_0)))&((X46!=k1_setfam_1(X45)|X46=k1_xboole_0|X45!=k1_xboole_0)&(X47!=k1_xboole_0|X47=k1_setfam_1(X45)|X45!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.20/0.42  cnf(c_0_31, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X1,X1,X1,X3)), inference(er,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_32, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_33, plain, (X1=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_21]), c_0_21]), c_0_21]), c_0_18]), c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_19])).
% 0.20/0.42  cnf(c_0_34, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|X3!=k1_xboole_0|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.42  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_37, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_38, plain, (X1=X2|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.42  cnf(c_0_39, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  fof(c_0_40, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.20/0.42  cnf(c_0_41, plain, (r2_hidden(esk1_2(X1,X2),k2_enumset1(X3,X3,X3,X3))|r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.42  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|r2_hidden(X3,X1)|X4!=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(X3,X4)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.42  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk3_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.42  cnf(c_0_44, plain, (esk3_3(k2_enumset1(X1,X1,X1,X1),X2,X3)=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r2_hidden(X3,X2)|X2!=k1_setfam_1(k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.42  fof(c_0_45, negated_conjecture, k1_setfam_1(k1_tarski(esk6_0))!=esk6_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_40])])])).
% 0.20/0.42  cnf(c_0_46, plain, (X1=esk1_2(X2,X3)|r1_tarski(X2,X3)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_41])).
% 0.20/0.42  cnf(c_0_47, plain, (k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|r2_hidden(X3,X1)|~r2_hidden(X3,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(er,[status(thm)],[c_0_42])).
% 0.20/0.42  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r2_hidden(X2,X3)|X3!=k1_setfam_1(k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (k1_setfam_1(k1_tarski(esk6_0))!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.42  cnf(c_0_50, plain, (X1=X2|r1_tarski(X3,X4)|X3!=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_46])).
% 0.20/0.42  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  fof(c_0_52, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.42  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.42  cnf(c_0_54, plain, (k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3),X1)|r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3)), inference(spm,[status(thm)],[c_0_47, c_0_35])).
% 0.20/0.42  cnf(c_0_55, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r2_hidden(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))|~r2_hidden(X2,X1)), inference(er,[status(thm)],[c_0_48])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_21]), c_0_18]), c_0_19])).
% 0.20/0.42  cnf(c_0_57, plain, (X1=X2|r1_tarski(k1_xboole_0,X3)), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.42  cnf(c_0_58, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_21]), c_0_18]), c_0_19])).
% 0.20/0.42  cnf(c_0_59, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.42  cnf(c_0_60, plain, (k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.42  cnf(c_0_61, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))|~r2_hidden(esk1_2(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))),X1)), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 0.20/0.42  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_57])).
% 0.20/0.42  cnf(c_0_63, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)|r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3)), inference(spm,[status(thm)],[c_0_58, c_0_35])).
% 0.20/0.42  cnf(c_0_64, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1|k2_enumset1(X1,X1,X1,X2)=k1_xboole_0|~r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.42  cnf(c_0_65, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_61, c_0_35])).
% 0.20/0.42  cnf(c_0_66, negated_conjecture, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_62])).
% 0.20/0.42  cnf(c_0_67, plain, (r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X1)), inference(spm,[status(thm)],[c_0_53, c_0_63])).
% 0.20/0.42  cnf(c_0_68, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.42  cnf(c_0_69, negated_conjecture, (k4_xboole_0(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_68])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_69])).
% 0.20/0.42  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_70]), c_0_71]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 73
% 0.20/0.42  # Proof object clause steps            : 50
% 0.20/0.42  # Proof object formula steps           : 23
% 0.20/0.42  # Proof object conjectures             : 11
% 0.20/0.42  # Proof object clause conjectures      : 8
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 16
% 0.20/0.42  # Proof object initial formulas used   : 11
% 0.20/0.42  # Proof object generating inferences   : 26
% 0.20/0.42  # Proof object simplifying inferences  : 27
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 11
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 32
% 0.20/0.42  # Removed in clause preprocessing      : 3
% 0.20/0.42  # Initial clauses in saturation        : 29
% 0.20/0.42  # Processed clauses                    : 553
% 0.20/0.42  # ...of these trivial                  : 9
% 0.20/0.42  # ...subsumed                          : 303
% 0.20/0.42  # ...remaining for further processing  : 241
% 0.20/0.42  # Other redundant clauses eliminated   : 64
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 9
% 0.20/0.42  # Backward-rewritten                   : 8
% 0.20/0.42  # Generated clauses                    : 2452
% 0.20/0.42  # ...of the previous two non-trivial   : 2052
% 0.20/0.42  # Contextual simplify-reflections      : 16
% 0.20/0.42  # Paramodulations                      : 2339
% 0.20/0.42  # Factorizations                       : 22
% 0.20/0.42  # Equation resolutions                 : 91
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 190
% 0.20/0.42  #    Positive orientable unit clauses  : 12
% 0.20/0.42  #    Positive unorientable unit clauses: 1
% 0.20/0.42  #    Negative unit clauses             : 3
% 0.20/0.42  #    Non-unit-clauses                  : 174
% 0.20/0.42  # Current number of unprocessed clauses: 1342
% 0.20/0.42  # ...number of literals in the above   : 6430
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 48
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 4332
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 2553
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 297
% 0.20/0.42  # Unit Clause-clause subsumption calls : 110
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 50
% 0.20/0.42  # BW rewrite match successes           : 39
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 38293
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.076 s
% 0.20/0.42  # System time              : 0.003 s
% 0.20/0.42  # Total time               : 0.079 s
% 0.20/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
