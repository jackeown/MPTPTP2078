%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:12 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   86 (1911 expanded)
%              Number of clauses        :   61 ( 900 expanded)
%              Number of leaves         :   12 ( 501 expanded)
%              Depth                    :   23
%              Number of atoms          :  225 (4651 expanded)
%              Number of equality atoms :   97 (2454 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t8_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(k1_setfam_1(X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t6_setfam_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X2,X3) )
     => ( X1 = k1_xboole_0
        | r1_tarski(X2,k1_setfam_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(c_0_12,plain,(
    ! [X37,X38] :
      ( ( ~ r1_tarski(X37,k1_tarski(X38))
        | X37 = k1_xboole_0
        | X37 = k1_tarski(X38) )
      & ( X37 != k1_xboole_0
        | r1_tarski(X37,k1_tarski(X38)) )
      & ( X37 != k1_tarski(X38)
        | r1_tarski(X37,k1_tarski(X38)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_14,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ( ~ r1_tarski(k1_tarski(X35),X36)
        | r2_hidden(X35,X36) )
      & ( ~ r2_hidden(X35,X36)
        | r1_tarski(k1_tarski(X35),X36) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_26,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X23,X22)
        | X23 = X20
        | X23 = X21
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X20
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( X24 != X21
        | r2_hidden(X24,X22)
        | X22 != k2_tarski(X20,X21) )
      & ( esk3_3(X25,X26,X27) != X25
        | ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( esk3_3(X25,X26,X27) != X26
        | ~ r2_hidden(esk3_3(X25,X26,X27),X27)
        | X27 = k2_tarski(X25,X26) )
      & ( r2_hidden(esk3_3(X25,X26,X27),X27)
        | esk3_3(X25,X26,X27) = X25
        | esk3_3(X25,X26,X27) = X26
        | X27 = k2_tarski(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | ~ r1_tarski(k2_enumset1(X1,X1,X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_34,plain,(
    ! [X42,X43,X44] :
      ( ~ r2_hidden(X42,X43)
      | ~ r1_tarski(X42,X44)
      | r1_tarski(k1_setfam_1(X43),X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_18]),c_0_19])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_setfam_1(X2),X3)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_18]),c_0_19])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X3)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_44])).

fof(c_0_48,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_45])).

cnf(c_0_50,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | r1_tarski(k1_xboole_0,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_17]),c_0_18]),c_0_19])).

fof(c_0_54,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_56,plain,
    ( r1_tarski(k1_setfam_1(X1),X2)
    | r1_tarski(X1,X3)
    | ~ r1_tarski(esk1_2(X1,X3),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

fof(c_0_58,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(ef,[status(thm)],[c_0_55])).

cnf(c_0_60,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_setfam_1(X1),esk1_2(X1,X2))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_47])).

cnf(c_0_62,plain,
    ( esk1_2(k2_enumset1(X1,X1,X1,X1),X2) = X1
    | r1_tarski(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_38])).

cnf(c_0_63,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_59])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_enumset1(X3,X3,X3,X1),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_40])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)),X1)
    | r1_tarski(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_67,plain,(
    ! [X39,X40] :
      ( ( r2_hidden(esk4_2(X39,X40),X39)
        | X39 = k1_xboole_0
        | r1_tarski(X40,k1_setfam_1(X39)) )
      & ( ~ r1_tarski(X40,esk4_2(X39,X40))
        | X39 = k1_xboole_0
        | r1_tarski(X40,k1_setfam_1(X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).

cnf(c_0_68,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_69,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = k1_xboole_0
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_43])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X1 = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_64])).

cnf(c_0_73,plain,
    ( X1 = X2
    | r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_70])).

cnf(c_0_74,plain,
    ( esk4_2(k2_enumset1(X1,X1,X1,X1),X2) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),esk5_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,plain,
    ( esk4_2(k2_enumset1(X1,X1,X1,X1),X2) = X1
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X2
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_59])).

cnf(c_0_78,plain,
    ( X2 = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(X2))
    | ~ r1_tarski(X1,esk4_2(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0) = esk5_0
    | k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_77]),c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_47])]),c_0_80])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_81]),c_0_59])])).

cnf(c_0_83,negated_conjecture,
    ( k1_setfam_1(k1_xboole_0) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_68,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( esk5_0 = X1 ),
    inference(spm,[status(thm)],[c_0_57,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.47/1.65  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.47/1.65  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.47/1.65  #
% 1.47/1.65  # Preprocessing time       : 0.029 s
% 1.47/1.65  # Presaturation interreduction done
% 1.47/1.65  
% 1.47/1.65  # Proof found!
% 1.47/1.65  # SZS status Theorem
% 1.47/1.65  # SZS output start CNFRefutation
% 1.47/1.65  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.47/1.65  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.47/1.65  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.47/1.65  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.47/1.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.47/1.65  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.47/1.65  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.47/1.65  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.47/1.65  fof(t8_setfam_1, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(k1_setfam_1(X2),X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_setfam_1)).
% 1.47/1.65  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.47/1.65  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.47/1.65  fof(t6_setfam_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X2,X3))=>(X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_setfam_1)).
% 1.47/1.65  fof(c_0_12, plain, ![X37, X38]:((~r1_tarski(X37,k1_tarski(X38))|(X37=k1_xboole_0|X37=k1_tarski(X38)))&((X37!=k1_xboole_0|r1_tarski(X37,k1_tarski(X38)))&(X37!=k1_tarski(X38)|r1_tarski(X37,k1_tarski(X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 1.47/1.65  fof(c_0_13, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.47/1.65  fof(c_0_14, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.47/1.65  fof(c_0_15, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.47/1.65  cnf(c_0_16, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.47/1.65  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.47/1.65  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.47/1.65  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.47/1.65  fof(c_0_20, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.47/1.65  cnf(c_0_21, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])).
% 1.47/1.65  fof(c_0_22, plain, ![X35, X36]:((~r1_tarski(k1_tarski(X35),X36)|r2_hidden(X35,X36))&(~r2_hidden(X35,X36)|r1_tarski(k1_tarski(X35),X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 1.47/1.65  cnf(c_0_23, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.47/1.65  cnf(c_0_24, plain, (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_21])).
% 1.47/1.65  cnf(c_0_25, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.47/1.65  fof(c_0_26, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X23,X22)|(X23=X20|X23=X21)|X22!=k2_tarski(X20,X21))&((X24!=X20|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))&(X24!=X21|r2_hidden(X24,X22)|X22!=k2_tarski(X20,X21))))&(((esk3_3(X25,X26,X27)!=X25|~r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26))&(esk3_3(X25,X26,X27)!=X26|~r2_hidden(esk3_3(X25,X26,X27),X27)|X27=k2_tarski(X25,X26)))&(r2_hidden(esk3_3(X25,X26,X27),X27)|(esk3_3(X25,X26,X27)=X25|esk3_3(X25,X26,X27)=X26)|X27=k2_tarski(X25,X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 1.47/1.65  cnf(c_0_27, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.47/1.65  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|~r1_tarski(k2_enumset1(X1,X1,X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 1.47/1.65  cnf(c_0_29, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19])).
% 1.47/1.65  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.47/1.65  cnf(c_0_31, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 1.47/1.65  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 1.47/1.65  fof(c_0_33, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.47/1.65  fof(c_0_34, plain, ![X42, X43, X44]:(~r2_hidden(X42,X43)|~r1_tarski(X42,X44)|r1_tarski(k1_setfam_1(X43),X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_setfam_1])])).
% 1.47/1.65  cnf(c_0_35, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_18]), c_0_19])).
% 1.47/1.65  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.47/1.65  cnf(c_0_37, plain, (X1=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.47/1.65  cnf(c_0_38, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.47/1.65  cnf(c_0_39, plain, (r1_tarski(k1_setfam_1(X2),X3)|~r2_hidden(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.47/1.65  cnf(c_0_40, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_35])])).
% 1.47/1.65  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_18]), c_0_19])).
% 1.47/1.65  cnf(c_0_42, plain, (X1=k1_xboole_0|r1_tarski(k1_xboole_0,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.47/1.65  cnf(c_0_43, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3)|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.47/1.65  cnf(c_0_44, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.47/1.65  cnf(c_0_45, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 1.47/1.65  cnf(c_0_46, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_xboole_0|r1_tarski(k1_xboole_0,X3)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.47/1.65  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_44])).
% 1.47/1.65  fof(c_0_48, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.47/1.65  cnf(c_0_49, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X3)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_39, c_0_45])).
% 1.47/1.65  cnf(c_0_50, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,k1_xboole_0))=k1_xboole_0|r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.47/1.65  cnf(c_0_51, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.47/1.65  cnf(c_0_52, plain, (r1_tarski(k1_xboole_0,X1)|r1_tarski(k1_xboole_0,X2)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.47/1.65  cnf(c_0_53, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_17]), c_0_18]), c_0_19])).
% 1.47/1.65  fof(c_0_54, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 1.47/1.65  cnf(c_0_55, plain, (r1_tarski(k1_xboole_0,X1)|r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_52, c_0_47])).
% 1.47/1.65  cnf(c_0_56, plain, (r1_tarski(k1_setfam_1(X1),X2)|r1_tarski(X1,X3)|~r1_tarski(esk1_2(X1,X3),X2)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 1.47/1.65  cnf(c_0_57, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_53])).
% 1.47/1.65  fof(c_0_58, negated_conjecture, k1_setfam_1(k1_tarski(esk5_0))!=esk5_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_54])])])).
% 1.47/1.65  cnf(c_0_59, plain, (r1_tarski(k1_xboole_0,X1)), inference(ef,[status(thm)],[c_0_55])).
% 1.47/1.65  cnf(c_0_60, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.47/1.65  cnf(c_0_61, plain, (r1_tarski(k1_setfam_1(X1),esk1_2(X1,X2))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_56, c_0_47])).
% 1.47/1.65  cnf(c_0_62, plain, (esk1_2(k2_enumset1(X1,X1,X1,X1),X2)=X1|r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)), inference(spm,[status(thm)],[c_0_57, c_0_38])).
% 1.47/1.65  cnf(c_0_63, negated_conjecture, (k1_setfam_1(k1_tarski(esk5_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.47/1.65  cnf(c_0_64, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_59])).
% 1.47/1.65  cnf(c_0_65, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_enumset1(X3,X3,X3,X1),X2)), inference(spm,[status(thm)],[c_0_60, c_0_40])).
% 1.47/1.65  cnf(c_0_66, plain, (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)),X1)|r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 1.47/1.65  fof(c_0_67, plain, ![X39, X40]:((r2_hidden(esk4_2(X39,X40),X39)|(X39=k1_xboole_0|r1_tarski(X40,k1_setfam_1(X39))))&(~r1_tarski(X40,esk4_2(X39,X40))|(X39=k1_xboole_0|r1_tarski(X40,k1_setfam_1(X39))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_setfam_1])])])])).
% 1.47/1.65  cnf(c_0_68, negated_conjecture, (k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_17]), c_0_18]), c_0_19])).
% 1.47/1.65  cnf(c_0_69, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=k1_xboole_0|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_43])).
% 1.47/1.65  cnf(c_0_70, plain, (r2_hidden(X1,X2)|r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)),X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.47/1.65  cnf(c_0_71, plain, (r2_hidden(esk4_2(X1,X2),X1)|X1=k1_xboole_0|r1_tarski(X2,k1_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.47/1.65  cnf(c_0_72, negated_conjecture, (~r1_tarski(esk5_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_64])).
% 1.47/1.65  cnf(c_0_73, plain, (X1=X2|r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)),X1)), inference(spm,[status(thm)],[c_0_57, c_0_70])).
% 1.47/1.65  cnf(c_0_74, plain, (esk4_2(k2_enumset1(X1,X1,X1,X1),X2)=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_57, c_0_71])).
% 1.47/1.65  cnf(c_0_75, negated_conjecture, (r1_tarski(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),esk5_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.47/1.65  cnf(c_0_76, plain, (esk4_2(k2_enumset1(X1,X1,X1,X1),X2)=X1|k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X2|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|~r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X1)),X2)), inference(spm,[status(thm)],[c_0_23, c_0_74])).
% 1.47/1.65  cnf(c_0_77, negated_conjecture, (r1_tarski(k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)),esk5_0)), inference(spm,[status(thm)],[c_0_75, c_0_59])).
% 1.47/1.65  cnf(c_0_78, plain, (X2=k1_xboole_0|r1_tarski(X1,k1_setfam_1(X2))|~r1_tarski(X1,esk4_2(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.47/1.65  cnf(c_0_79, negated_conjecture, (esk4_2(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk5_0)=esk5_0|k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_68])).
% 1.47/1.65  cnf(c_0_80, negated_conjecture, (~r1_tarski(esk5_0,k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_77]), c_0_68])).
% 1.47/1.65  cnf(c_0_81, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_47])]), c_0_80])).
% 1.47/1.65  cnf(c_0_82, negated_conjecture, (r2_hidden(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_81]), c_0_59])])).
% 1.47/1.65  cnf(c_0_83, negated_conjecture, (k1_setfam_1(k1_xboole_0)!=esk5_0), inference(rw,[status(thm)],[c_0_68, c_0_81])).
% 1.47/1.65  cnf(c_0_84, negated_conjecture, (esk5_0=X1), inference(spm,[status(thm)],[c_0_57, c_0_82])).
% 1.47/1.65  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_84])]), ['proof']).
% 1.47/1.65  # SZS output end CNFRefutation
% 1.47/1.65  # Proof object total steps             : 86
% 1.47/1.65  # Proof object clause steps            : 61
% 1.47/1.65  # Proof object formula steps           : 25
% 1.47/1.65  # Proof object conjectures             : 15
% 1.47/1.65  # Proof object clause conjectures      : 12
% 1.47/1.65  # Proof object formula conjectures     : 3
% 1.47/1.65  # Proof object initial clauses used    : 17
% 1.47/1.65  # Proof object initial formulas used   : 12
% 1.47/1.65  # Proof object generating inferences   : 30
% 1.47/1.65  # Proof object simplifying inferences  : 40
% 1.47/1.65  # Training examples: 0 positive, 0 negative
% 1.47/1.65  # Parsed axioms                        : 12
% 1.47/1.65  # Removed by relevancy pruning/SinE    : 0
% 1.47/1.65  # Initial clauses                      : 28
% 1.47/1.65  # Removed in clause preprocessing      : 3
% 1.47/1.65  # Initial clauses in saturation        : 25
% 1.47/1.65  # Processed clauses                    : 1965
% 1.47/1.65  # ...of these trivial                  : 12
% 1.47/1.65  # ...subsumed                          : 1005
% 1.47/1.65  # ...remaining for further processing  : 948
% 1.47/1.65  # Other redundant clauses eliminated   : 2223
% 1.47/1.65  # Clauses deleted for lack of memory   : 0
% 1.47/1.65  # Backward-subsumed                    : 205
% 1.47/1.65  # Backward-rewritten                   : 701
% 1.47/1.65  # Generated clauses                    : 78074
% 1.47/1.65  # ...of the previous two non-trivial   : 73493
% 1.47/1.65  # Contextual simplify-reflections      : 24
% 1.47/1.65  # Paramodulations                      : 75676
% 1.47/1.65  # Factorizations                       : 177
% 1.47/1.65  # Equation resolutions                 : 2223
% 1.47/1.65  # Propositional unsat checks           : 0
% 1.47/1.65  #    Propositional check models        : 0
% 1.47/1.65  #    Propositional check unsatisfiable : 0
% 1.47/1.65  #    Propositional clauses             : 0
% 1.47/1.65  #    Propositional clauses after purity: 0
% 1.47/1.65  #    Propositional unsat core size     : 0
% 1.47/1.65  #    Propositional preprocessing time  : 0.000
% 1.47/1.65  #    Propositional encoding time       : 0.000
% 1.47/1.65  #    Propositional solver time         : 0.000
% 1.47/1.65  #    Success case prop preproc time    : 0.000
% 1.47/1.65  #    Success case prop encoding time   : 0.000
% 1.47/1.65  #    Success case prop solver time     : 0.000
% 1.47/1.65  # Current number of processed clauses  : 10
% 1.47/1.65  #    Positive orientable unit clauses  : 3
% 1.47/1.65  #    Positive unorientable unit clauses: 1
% 1.47/1.65  #    Negative unit clauses             : 2
% 1.47/1.65  #    Non-unit-clauses                  : 4
% 1.47/1.65  # Current number of unprocessed clauses: 67805
% 1.47/1.65  # ...number of literals in the above   : 523630
% 1.47/1.65  # Current number of archived formulas  : 0
% 1.47/1.65  # Current number of archived clauses   : 932
% 1.47/1.65  # Clause-clause subsumption calls (NU) : 31961
% 1.47/1.65  # Rec. Clause-clause subsumption calls : 10879
% 1.47/1.65  # Non-unit clause-clause subsumptions  : 1069
% 1.47/1.65  # Unit Clause-clause subsumption calls : 1142
% 1.47/1.65  # Rewrite failures with RHS unbound    : 3
% 1.47/1.65  # BW rewrite match attempts            : 290
% 1.47/1.65  # BW rewrite match successes           : 222
% 1.47/1.65  # Condensation attempts                : 0
% 1.47/1.65  # Condensation successes               : 0
% 1.47/1.65  # Termbank termtop insertions          : 2073747
% 1.47/1.65  
% 1.47/1.65  # -------------------------------------------------
% 1.47/1.65  # User time                : 1.272 s
% 1.47/1.65  # System time              : 0.034 s
% 1.47/1.65  # Total time               : 1.306 s
% 1.47/1.65  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
