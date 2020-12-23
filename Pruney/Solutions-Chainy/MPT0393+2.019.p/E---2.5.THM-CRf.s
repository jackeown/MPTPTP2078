%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:11 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 252 expanded)
%              Number of clauses        :   43 ( 111 expanded)
%              Number of leaves         :   11 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  198 ( 615 expanded)
%              Number of equality atoms :  123 ( 424 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t20_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
    <=> X1 != X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(c_0_11,plain,(
    ! [X24,X25] :
      ( ( ~ r1_tarski(X24,k1_tarski(X25))
        | X24 = k1_xboole_0
        | X24 = k1_tarski(X25) )
      & ( X24 != k1_xboole_0
        | r1_tarski(X24,k1_tarski(X25)) )
      & ( X24 != k1_tarski(X25)
        | r1_tarski(X24,k1_tarski(X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,plain,(
    ! [X28,X29] :
      ( ( k4_xboole_0(X28,k1_tarski(X29)) != X28
        | ~ r2_hidden(X29,X28) )
      & ( r2_hidden(X29,X28)
        | k4_xboole_0(X28,k1_tarski(X29)) = X28 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X9
        | X12 = X10
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( esk1_3(X14,X15,X16) != X14
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( esk1_3(X14,X15,X16) != X15
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X16)
        | esk1_3(X14,X15,X16) = X14
        | esk1_3(X14,X15,X16) = X15
        | X16 = k2_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,k1_tarski(X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X30,X31,X32,X33,X34,X36,X39,X40,X41,X42] :
      ( ( ~ r2_hidden(X32,X31)
        | ~ r2_hidden(X33,X30)
        | r2_hidden(X32,X33)
        | X31 != k1_setfam_1(X30)
        | X30 = k1_xboole_0 )
      & ( r2_hidden(esk2_3(X30,X31,X34),X30)
        | r2_hidden(X34,X31)
        | X31 != k1_setfam_1(X30)
        | X30 = k1_xboole_0 )
      & ( ~ r2_hidden(X34,esk2_3(X30,X31,X34))
        | r2_hidden(X34,X31)
        | X31 != k1_setfam_1(X30)
        | X30 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X30,X36),X30)
        | ~ r2_hidden(esk3_2(X30,X36),X36)
        | X36 = k1_setfam_1(X30)
        | X30 = k1_xboole_0 )
      & ( ~ r2_hidden(esk3_2(X30,X36),esk4_2(X30,X36))
        | ~ r2_hidden(esk3_2(X30,X36),X36)
        | X36 = k1_setfam_1(X30)
        | X30 = k1_xboole_0 )
      & ( r2_hidden(esk3_2(X30,X36),X36)
        | ~ r2_hidden(X39,X30)
        | r2_hidden(esk3_2(X30,X36),X39)
        | X36 = k1_setfam_1(X30)
        | X30 = k1_xboole_0 )
      & ( X41 != k1_setfam_1(X40)
        | X41 = k1_xboole_0
        | X40 != k1_xboole_0 )
      & ( X42 != k1_xboole_0
        | X42 = k1_setfam_1(X40)
        | X40 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) != X1
    | ~ r2_hidden(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_19]),c_0_20])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(esk3_2(X1,X2),X3)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( k1_xboole_0 != X1
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X3,X3,X3,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_34,plain,(
    ! [X26,X27] :
      ( ( k4_xboole_0(k1_tarski(X26),k1_tarski(X27)) != k1_tarski(X26)
        | X26 != X27 )
      & ( X26 = X27
        | k4_xboole_0(k1_tarski(X26),k1_tarski(X27)) = k1_tarski(X26) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).

cnf(c_0_35,plain,
    ( X1 = k1_setfam_1(X2)
    | r2_hidden(esk3_2(X2,X1),X3)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_19]),c_0_20])).

cnf(c_0_39,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( X1 = k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | r2_hidden(esk3_2(k2_enumset1(X2,X2,X2,X3),X1),X1)
    | r2_hidden(esk3_2(k2_enumset1(X2,X2,X2,X3),X1),X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1)
    | X1 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X1,X1,X1,X3) ),
    inference(er,[status(thm)],[c_0_38])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_45,plain,
    ( X1 = X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_18]),c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_46,plain,
    ( r2_hidden(esk4_2(X1,X2),X1)
    | X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk3_2(k2_enumset1(X1,X1,X1,X2),X2),X2) ),
    inference(ef,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X1,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_49,plain,
    ( X1 != X2
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_18]),c_0_18]),c_0_18]),c_0_19]),c_0_19]),c_0_19]),c_0_20]),c_0_20]),c_0_20])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_43])).

fof(c_0_52,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_45])).

cnf(c_0_54,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X2
    | r2_hidden(esk4_2(k2_enumset1(X1,X1,X1,X2),X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_55,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) != k2_enumset1(X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_50])).

cnf(c_0_57,plain,
    ( X1 = k1_setfam_1(k2_enumset1(X2,X2,X2,X3))
    | r2_hidden(esk3_2(k2_enumset1(X2,X2,X2,X3),X1),X1)
    | r2_hidden(esk3_2(k2_enumset1(X2,X2,X2,X3),X1),X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk5_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( X2 = k1_setfam_1(X1)
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_60,plain,
    ( esk4_2(k2_enumset1(X1,X1,X1,X1),X1) = X1
    | k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_62,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) = X1
    | r2_hidden(esk3_2(k2_enumset1(X1,X1,X1,X2),X1),X1) ),
    inference(ef,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_18]),c_0_19]),c_0_20])).

cnf(c_0_64,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:52:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.67  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.47/0.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.47/0.67  #
% 0.47/0.67  # Preprocessing time       : 0.029 s
% 0.47/0.67  # Presaturation interreduction done
% 0.47/0.67  
% 0.47/0.67  # Proof found!
% 0.47/0.67  # SZS status Theorem
% 0.47/0.67  # SZS output start CNFRefutation
% 0.47/0.67  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.47/0.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.47/0.67  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.47/0.67  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.47/0.67  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.47/0.67  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.47/0.67  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.47/0.67  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.47/0.67  fof(t20_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)<=>X1!=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 0.47/0.67  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.67  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.47/0.67  fof(c_0_11, plain, ![X24, X25]:((~r1_tarski(X24,k1_tarski(X25))|(X24=k1_xboole_0|X24=k1_tarski(X25)))&((X24!=k1_xboole_0|r1_tarski(X24,k1_tarski(X25)))&(X24!=k1_tarski(X25)|r1_tarski(X24,k1_tarski(X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.47/0.67  fof(c_0_12, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.47/0.67  fof(c_0_13, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.47/0.67  fof(c_0_14, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.47/0.67  fof(c_0_15, plain, ![X28, X29]:((k4_xboole_0(X28,k1_tarski(X29))!=X28|~r2_hidden(X29,X28))&(r2_hidden(X29,X28)|k4_xboole_0(X28,k1_tarski(X29))=X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.47/0.67  fof(c_0_16, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.47/0.67  cnf(c_0_17, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.47/0.67  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.47/0.67  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.47/0.67  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.47/0.67  fof(c_0_21, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(X12=X9|X12=X10)|X11!=k2_tarski(X9,X10))&((X13!=X9|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))))&(((esk1_3(X14,X15,X16)!=X14|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15))&(esk1_3(X14,X15,X16)!=X15|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15)))&(r2_hidden(esk1_3(X14,X15,X16),X16)|(esk1_3(X14,X15,X16)=X14|esk1_3(X14,X15,X16)=X15)|X16=k2_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.47/0.67  cnf(c_0_22, plain, (k4_xboole_0(X1,k1_tarski(X2))!=X1|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.47/0.67  cnf(c_0_23, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.47/0.67  cnf(c_0_24, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])).
% 0.47/0.67  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.67  fof(c_0_26, plain, ![X30, X31, X32, X33, X34, X36, X39, X40, X41, X42]:((((~r2_hidden(X32,X31)|(~r2_hidden(X33,X30)|r2_hidden(X32,X33))|X31!=k1_setfam_1(X30)|X30=k1_xboole_0)&((r2_hidden(esk2_3(X30,X31,X34),X30)|r2_hidden(X34,X31)|X31!=k1_setfam_1(X30)|X30=k1_xboole_0)&(~r2_hidden(X34,esk2_3(X30,X31,X34))|r2_hidden(X34,X31)|X31!=k1_setfam_1(X30)|X30=k1_xboole_0)))&(((r2_hidden(esk4_2(X30,X36),X30)|~r2_hidden(esk3_2(X30,X36),X36)|X36=k1_setfam_1(X30)|X30=k1_xboole_0)&(~r2_hidden(esk3_2(X30,X36),esk4_2(X30,X36))|~r2_hidden(esk3_2(X30,X36),X36)|X36=k1_setfam_1(X30)|X30=k1_xboole_0))&(r2_hidden(esk3_2(X30,X36),X36)|(~r2_hidden(X39,X30)|r2_hidden(esk3_2(X30,X36),X39))|X36=k1_setfam_1(X30)|X30=k1_xboole_0)))&((X41!=k1_setfam_1(X40)|X41=k1_xboole_0|X40!=k1_xboole_0)&(X42!=k1_xboole_0|X42=k1_setfam_1(X40)|X40!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.47/0.67  cnf(c_0_27, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))!=X1|~r2_hidden(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_18]), c_0_19]), c_0_20])).
% 0.47/0.67  cnf(c_0_28, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.47/0.67  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_19]), c_0_20])).
% 0.47/0.67  cnf(c_0_30, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(esk3_2(X1,X2),X3)|X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.67  cnf(c_0_31, plain, (k1_xboole_0!=X1|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.47/0.67  cnf(c_0_32, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X3,X3,X3,X1)), inference(er,[status(thm)],[c_0_29])).
% 0.47/0.67  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.67  fof(c_0_34, plain, ![X26, X27]:((k4_xboole_0(k1_tarski(X26),k1_tarski(X27))!=k1_tarski(X26)|X26!=X27)&(X26=X27|k4_xboole_0(k1_tarski(X26),k1_tarski(X27))=k1_tarski(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_zfmisc_1])])).
% 0.47/0.67  cnf(c_0_35, plain, (X1=k1_setfam_1(X2)|r2_hidden(esk3_2(X2,X1),X3)|r2_hidden(esk3_2(X2,X1),X1)|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_30, c_0_31])).
% 0.47/0.67  cnf(c_0_36, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_32])).
% 0.47/0.67  fof(c_0_37, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.67  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_19]), c_0_20])).
% 0.47/0.67  cnf(c_0_39, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.67  cnf(c_0_40, plain, (X1=k1_setfam_1(k2_enumset1(X2,X2,X2,X3))|r2_hidden(esk3_2(k2_enumset1(X2,X2,X2,X3),X1),X1)|r2_hidden(esk3_2(k2_enumset1(X2,X2,X2,X3),X1),X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.47/0.67  cnf(c_0_41, plain, (k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)|X1!=X2), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.67  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.67  cnf(c_0_43, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X1,X1,X1,X3)), inference(er,[status(thm)],[c_0_38])).
% 0.47/0.67  fof(c_0_44, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.47/0.67  cnf(c_0_45, plain, (X1=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_18]), c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 0.47/0.67  cnf(c_0_46, plain, (r2_hidden(esk4_2(X1,X2),X1)|X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(esk3_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.67  cnf(c_0_47, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk3_2(k2_enumset1(X1,X1,X1,X2),X2),X2)), inference(ef,[status(thm)],[c_0_40])).
% 0.47/0.67  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X1,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 0.47/0.67  cnf(c_0_49, plain, (X1!=X2|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))!=k2_enumset1(X1,X1,X1,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_18]), c_0_18]), c_0_18]), c_0_19]), c_0_19]), c_0_19]), c_0_20]), c_0_20]), c_0_20])).
% 0.47/0.67  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.47/0.67  cnf(c_0_51, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_43])).
% 0.47/0.67  fof(c_0_52, negated_conjecture, k1_setfam_1(k1_tarski(esk5_0))!=esk5_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).
% 0.47/0.67  cnf(c_0_53, plain, (X1=X2|~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_27, c_0_45])).
% 0.47/0.67  cnf(c_0_54, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X2|r2_hidden(esk4_2(k2_enumset1(X1,X1,X1,X2),X2),k2_enumset1(X1,X1,X1,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.47/0.67  cnf(c_0_55, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))!=k2_enumset1(X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.47/0.67  cnf(c_0_56, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_50])).
% 0.47/0.67  cnf(c_0_57, plain, (X1=k1_setfam_1(k2_enumset1(X2,X2,X2,X3))|r2_hidden(esk3_2(k2_enumset1(X2,X2,X2,X3),X1),X1)|r2_hidden(esk3_2(k2_enumset1(X2,X2,X2,X3),X1),X2)), inference(spm,[status(thm)],[c_0_35, c_0_51])).
% 0.47/0.67  cnf(c_0_58, negated_conjecture, (k1_setfam_1(k1_tarski(esk5_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.47/0.67  cnf(c_0_59, plain, (X2=k1_setfam_1(X1)|X1=k1_xboole_0|~r2_hidden(esk3_2(X1,X2),esk4_2(X1,X2))|~r2_hidden(esk3_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.67  cnf(c_0_60, plain, (esk4_2(k2_enumset1(X1,X1,X1,X1),X1)=X1|k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.47/0.67  cnf(c_0_61, plain, (k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.47/0.67  cnf(c_0_62, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X2))=X1|r2_hidden(esk3_2(k2_enumset1(X1,X1,X1,X2),X1),X1)), inference(ef,[status(thm)],[c_0_57])).
% 0.47/0.67  cnf(c_0_63, negated_conjecture, (k1_setfam_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))!=esk5_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_18]), c_0_19]), c_0_20])).
% 0.47/0.67  cnf(c_0_64, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])).
% 0.47/0.67  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])]), ['proof']).
% 0.47/0.67  # SZS output end CNFRefutation
% 0.47/0.67  # Proof object total steps             : 66
% 0.47/0.67  # Proof object clause steps            : 43
% 0.47/0.67  # Proof object formula steps           : 23
% 0.47/0.67  # Proof object conjectures             : 6
% 0.47/0.67  # Proof object clause conjectures      : 3
% 0.47/0.67  # Proof object formula conjectures     : 3
% 0.47/0.67  # Proof object initial clauses used    : 15
% 0.47/0.67  # Proof object initial formulas used   : 11
% 0.47/0.67  # Proof object generating inferences   : 14
% 0.47/0.67  # Proof object simplifying inferences  : 42
% 0.47/0.67  # Training examples: 0 positive, 0 negative
% 0.47/0.67  # Parsed axioms                        : 11
% 0.47/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.67  # Initial clauses                      : 30
% 0.47/0.67  # Removed in clause preprocessing      : 3
% 0.47/0.67  # Initial clauses in saturation        : 27
% 0.47/0.67  # Processed clauses                    : 2056
% 0.47/0.67  # ...of these trivial                  : 41
% 0.47/0.67  # ...subsumed                          : 1503
% 0.47/0.67  # ...remaining for further processing  : 512
% 0.47/0.67  # Other redundant clauses eliminated   : 163
% 0.47/0.67  # Clauses deleted for lack of memory   : 0
% 0.47/0.67  # Backward-subsumed                    : 22
% 0.47/0.67  # Backward-rewritten                   : 110
% 0.47/0.67  # Generated clauses                    : 14951
% 0.47/0.67  # ...of the previous two non-trivial   : 13291
% 0.47/0.67  # Contextual simplify-reflections      : 23
% 0.47/0.67  # Paramodulations                      : 14589
% 0.47/0.67  # Factorizations                       : 62
% 0.47/0.67  # Equation resolutions                 : 300
% 0.47/0.67  # Propositional unsat checks           : 0
% 0.47/0.67  #    Propositional check models        : 0
% 0.47/0.67  #    Propositional check unsatisfiable : 0
% 0.47/0.67  #    Propositional clauses             : 0
% 0.47/0.67  #    Propositional clauses after purity: 0
% 0.47/0.67  #    Propositional unsat core size     : 0
% 0.47/0.67  #    Propositional preprocessing time  : 0.000
% 0.47/0.67  #    Propositional encoding time       : 0.000
% 0.47/0.67  #    Propositional solver time         : 0.000
% 0.47/0.67  #    Success case prop preproc time    : 0.000
% 0.47/0.67  #    Success case prop encoding time   : 0.000
% 0.47/0.67  #    Success case prop solver time     : 0.000
% 0.47/0.67  # Current number of processed clauses  : 349
% 0.47/0.67  #    Positive orientable unit clauses  : 11
% 0.47/0.67  #    Positive unorientable unit clauses: 0
% 0.47/0.67  #    Negative unit clauses             : 7
% 0.47/0.67  #    Non-unit-clauses                  : 331
% 0.47/0.67  # Current number of unprocessed clauses: 11072
% 0.47/0.67  # ...number of literals in the above   : 55200
% 0.47/0.67  # Current number of archived formulas  : 0
% 0.47/0.67  # Current number of archived clauses   : 161
% 0.47/0.67  # Clause-clause subsumption calls (NU) : 30970
% 0.47/0.67  # Rec. Clause-clause subsumption calls : 14842
% 0.47/0.67  # Non-unit clause-clause subsumptions  : 1138
% 0.47/0.67  # Unit Clause-clause subsumption calls : 276
% 0.47/0.67  # Rewrite failures with RHS unbound    : 0
% 0.47/0.67  # BW rewrite match attempts            : 77
% 0.47/0.67  # BW rewrite match successes           : 13
% 0.47/0.67  # Condensation attempts                : 0
% 0.47/0.67  # Condensation successes               : 0
% 0.47/0.67  # Termbank termtop insertions          : 361708
% 0.47/0.67  
% 0.47/0.67  # -------------------------------------------------
% 0.47/0.67  # User time                : 0.321 s
% 0.47/0.67  # System time              : 0.009 s
% 0.47/0.67  # Total time               : 0.330 s
% 0.47/0.67  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
