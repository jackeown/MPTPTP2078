%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:11 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :   92 (1082 expanded)
%              Number of clauses        :   63 ( 521 expanded)
%              Number of leaves         :   14 ( 273 expanded)
%              Depth                    :   24
%              Number of atoms          :  212 (2481 expanded)
%              Number of equality atoms :  124 (1166 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t51_xboole_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(t28_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
        & X1 != X3
        & X1 != X4 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t89_enumset1,axiom,(
    ! [X1,X2,X3] : k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(t25_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))
        & X1 != X2
        & X1 != X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(t9_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k1_tarski(X1) = k2_tarski(X2,X3)
     => X2 = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(t18_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(c_0_14,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_15,plain,(
    ! [X7,X8] :
      ( ( k4_xboole_0(X7,X8) != k1_xboole_0
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | k4_xboole_0(X7,X8) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X9,X10] : k2_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(X9,X10)) = X9 ),
    inference(variable_rename,[status(thm)],[t51_xboole_1])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X12,X13,X14] :
      ( ( r1_xboole_0(X12,k2_xboole_0(X13,X14))
        | ~ r1_xboole_0(X12,X13)
        | ~ r1_xboole_0(X12,X14) )
      & ( r1_xboole_0(X12,X13)
        | ~ r1_xboole_0(X12,k2_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_xboole_0(X12,k2_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_21,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] :
      ( ~ r1_xboole_0(X15,k4_xboole_0(X16,X17))
      | r1_xboole_0(X16,k4_xboole_0(X15,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))
          & X1 != X3
          & X1 != X4 ) ),
    inference(assume_negation,[status(cth)],[t28_zfmisc_1])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X1),k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X11] :
      ( ( r1_xboole_0(X11,X11)
        | X11 != k1_xboole_0 )
      & ( X11 = k1_xboole_0
        | ~ r1_xboole_0(X11,X11) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_29,plain,(
    ! [X23,X24,X25] :
      ( ( ~ r1_tarski(X23,k2_tarski(X24,X25))
        | X23 = k1_xboole_0
        | X23 = k1_tarski(X24)
        | X23 = k1_tarski(X25)
        | X23 = k2_tarski(X24,X25) )
      & ( X23 != k1_xboole_0
        | r1_tarski(X23,k2_tarski(X24,X25)) )
      & ( X23 != k1_tarski(X24)
        | r1_tarski(X23,k2_tarski(X24,X25)) )
      & ( X23 != k1_tarski(X25)
        | r1_tarski(X23,k2_tarski(X24,X25)) )
      & ( X23 != k2_tarski(X24,X25)
        | r1_tarski(X23,k2_tarski(X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

fof(c_0_30,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_31,plain,(
    ! [X20,X21,X22] : k5_enumset1(X20,X20,X20,X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t89_enumset1])).

fof(c_0_32,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))
    & esk1_0 != esk3_0
    & esk1_0 != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_35,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X26,X27] : r1_tarski(k1_tarski(X26),k2_tarski(X26,X27)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k2_tarski(X2,X3)
    | ~ r1_tarski(X1,k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_21])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,k1_xboole_0)
    | ~ r1_xboole_0(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_35])).

fof(c_0_44,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(k1_tarski(X30),k2_tarski(X31,X32))
      | X30 = X31
      | X30 = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_zfmisc_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X2)
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X3)
    | ~ r1_tarski(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_38]),c_0_38]),c_0_39]),c_0_39])).

cnf(c_0_48,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_49,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_50,plain,(
    ! [X33,X34,X35] :
      ( k1_tarski(X33) != k2_tarski(X34,X35)
      | X34 = X35 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_zfmisc_1])])).

cnf(c_0_51,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r1_tarski(k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,plain,
    ( r1_tarski(k1_tarski(X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_38]),c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_tarski(esk3_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_tarski(esk4_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,k2_tarski(X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_56,plain,
    ( X2 = X3
    | k1_tarski(X1) != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,plain,
    ( X1 = X3
    | X1 = X2
    | ~ r1_tarski(k1_tarski(X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_38]),c_0_39])).

cnf(c_0_58,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_tarski(esk4_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_tarski(esk3_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | r1_tarski(k1_tarski(esk1_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( esk1_0 != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( esk1_0 != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_62,plain,
    ( r1_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_54])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | k4_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,k5_enumset1(X3,X3,X3,X3,X3,X3,X2))
    | X1 != k1_tarski(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_38]),c_0_39])).

cnf(c_0_66,plain,
    ( X2 = X3
    | k1_tarski(X1) != k5_enumset1(X2,X2,X2,X2,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_38]),c_0_39])).

cnf(c_0_67,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_tarski(esk3_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_tarski(esk4_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60])).

cnf(c_0_68,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( X1 = X2
    | k4_xboole_0(X2,X1) != k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_tarski(X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = esk1_0
    | k1_tarski(X1) != k1_tarski(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_66])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_73,plain,
    ( k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_68])).

fof(c_0_74,plain,(
    ! [X28,X29] :
      ( k3_xboole_0(k1_tarski(X28),k1_tarski(X29)) != k1_tarski(X28)
      | X28 = X29 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_zfmisc_1])])).

cnf(c_0_75,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k1_tarski(X2)
    | k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k1_tarski(X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0) = k1_xboole_0
    | esk2_0 = esk1_0 ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_77,plain,
    ( r1_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_49])])).

cnf(c_0_78,plain,
    ( X1 = X2
    | k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( k1_tarski(esk2_0) = k1_xboole_0
    | esk2_0 = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_68])])).

cnf(c_0_80,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( esk2_0 = esk1_0
    | esk2_0 = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])])).

cnf(c_0_82,negated_conjecture,
    ( esk2_0 = esk1_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_81])])).

cnf(c_0_83,negated_conjecture,
    ( k1_tarski(esk4_0) = k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)
    | k1_tarski(esk3_0) = k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_82]),c_0_82]),c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( k1_tarski(esk3_0) = k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | esk4_0 = X1
    | esk4_0 = X2
    | ~ r1_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( k1_tarski(esk3_0) = k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)
    | k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_19]),c_0_59])).

cnf(c_0_86,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0
    | esk3_0 = X1
    | esk3_0 = X2
    | ~ r1_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_85])).

cnf(c_0_87,plain,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = k1_tarski(X1)
    | k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k1_tarski(X1)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_52])).

cnf(c_0_88,negated_conjecture,
    ( k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_19]),c_0_60])).

cnf(c_0_89,negated_conjecture,
    ( k1_tarski(esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_68])])).

cnf(c_0_90,negated_conjecture,
    ( esk1_0 = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_89]),c_0_80])])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_90])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 5.94/6.15  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 5.94/6.15  # and selection function SelectMaxLComplexAvoidPosPred.
% 5.94/6.15  #
% 5.94/6.15  # Preprocessing time       : 0.028 s
% 5.94/6.15  # Presaturation interreduction done
% 5.94/6.15  
% 5.94/6.15  # Proof found!
% 5.94/6.15  # SZS status Theorem
% 5.94/6.15  # SZS output start CNFRefutation
% 5.94/6.15  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.94/6.15  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.94/6.15  fof(t51_xboole_1, axiom, ![X1, X2]:k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 5.94/6.15  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.94/6.15  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 5.94/6.15  fof(t28_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 5.94/6.15  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 5.94/6.15  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 5.94/6.15  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.94/6.15  fof(t89_enumset1, axiom, ![X1, X2, X3]:k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_enumset1)).
% 5.94/6.15  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 5.94/6.15  fof(t25_zfmisc_1, axiom, ![X1, X2, X3]:~(((r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))&X1!=X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 5.94/6.15  fof(t9_zfmisc_1, axiom, ![X1, X2, X3]:(k1_tarski(X1)=k2_tarski(X2,X3)=>X2=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 5.94/6.15  fof(t18_zfmisc_1, axiom, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 5.94/6.15  fof(c_0_14, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 5.94/6.15  fof(c_0_15, plain, ![X7, X8]:((k4_xboole_0(X7,X8)!=k1_xboole_0|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|k4_xboole_0(X7,X8)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 5.94/6.15  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.94/6.15  fof(c_0_17, plain, ![X9, X10]:k2_xboole_0(k3_xboole_0(X9,X10),k4_xboole_0(X9,X10))=X9, inference(variable_rename,[status(thm)],[t51_xboole_1])).
% 5.94/6.15  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.94/6.15  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 5.94/6.15  fof(c_0_20, plain, ![X12, X13, X14]:((r1_xboole_0(X12,k2_xboole_0(X13,X14))|~r1_xboole_0(X12,X13)|~r1_xboole_0(X12,X14))&((r1_xboole_0(X12,X13)|~r1_xboole_0(X12,k2_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_xboole_0(X12,k2_xboole_0(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 5.94/6.15  cnf(c_0_21, plain, (k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.94/6.15  cnf(c_0_22, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 5.94/6.15  fof(c_0_23, plain, ![X15, X16, X17]:(~r1_xboole_0(X15,k4_xboole_0(X16,X17))|r1_xboole_0(X16,k4_xboole_0(X15,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 5.94/6.15  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(k2_tarski(X1,X2),k2_tarski(X3,X4))&X1!=X3)&X1!=X4))), inference(assume_negation,[status(cth)],[t28_zfmisc_1])).
% 5.94/6.15  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.94/6.15  cnf(c_0_26, plain, (k2_xboole_0(k3_xboole_0(X1,X1),k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 5.94/6.15  cnf(c_0_27, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.94/6.15  fof(c_0_28, plain, ![X11]:((r1_xboole_0(X11,X11)|X11!=k1_xboole_0)&(X11=k1_xboole_0|~r1_xboole_0(X11,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 5.94/6.15  fof(c_0_29, plain, ![X23, X24, X25]:((~r1_tarski(X23,k2_tarski(X24,X25))|(X23=k1_xboole_0|X23=k1_tarski(X24)|X23=k1_tarski(X25)|X23=k2_tarski(X24,X25)))&((((X23!=k1_xboole_0|r1_tarski(X23,k2_tarski(X24,X25)))&(X23!=k1_tarski(X24)|r1_tarski(X23,k2_tarski(X24,X25))))&(X23!=k1_tarski(X25)|r1_tarski(X23,k2_tarski(X24,X25))))&(X23!=k2_tarski(X24,X25)|r1_tarski(X23,k2_tarski(X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 5.94/6.15  fof(c_0_30, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 5.94/6.15  fof(c_0_31, plain, ![X20, X21, X22]:k5_enumset1(X20,X20,X20,X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t89_enumset1])).
% 5.94/6.15  fof(c_0_32, negated_conjecture, ((r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))&esk1_0!=esk3_0)&esk1_0!=esk4_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 5.94/6.15  cnf(c_0_33, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 5.94/6.15  cnf(c_0_34, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 5.94/6.15  cnf(c_0_35, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 5.94/6.15  fof(c_0_36, plain, ![X26, X27]:r1_tarski(k1_tarski(X26),k2_tarski(X26,X27)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 5.94/6.15  cnf(c_0_37, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k2_tarski(X2,X3)|~r1_tarski(X1,k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.94/6.15  cnf(c_0_38, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 5.94/6.15  cnf(c_0_39, plain, (k5_enumset1(X1,X1,X1,X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.94/6.15  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_tarski(esk1_0,esk2_0),k2_tarski(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.94/6.15  cnf(c_0_41, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_21])).
% 5.94/6.15  cnf(c_0_42, plain, (r1_xboole_0(X1,k1_xboole_0)|~r1_xboole_0(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 5.94/6.15  cnf(c_0_43, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_35])).
% 5.94/6.15  fof(c_0_44, plain, ![X30, X31, X32]:(~r1_tarski(k1_tarski(X30),k2_tarski(X31,X32))|X30=X31|X30=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_zfmisc_1])])).
% 5.94/6.15  cnf(c_0_45, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 5.94/6.15  cnf(c_0_46, plain, (X1=k1_xboole_0|X1=k1_tarski(X3)|X1=k1_tarski(X2)|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X3)|~r1_tarski(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 5.94/6.15  cnf(c_0_47, negated_conjecture, (r1_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_38]), c_0_38]), c_0_39]), c_0_39])).
% 5.94/6.15  cnf(c_0_48, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 5.94/6.15  cnf(c_0_49, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 5.94/6.15  fof(c_0_50, plain, ![X33, X34, X35]:(k1_tarski(X33)!=k2_tarski(X34,X35)|X34=X35), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_zfmisc_1])])).
% 5.94/6.15  cnf(c_0_51, plain, (X1=X2|X1=X3|~r1_tarski(k1_tarski(X1),k2_tarski(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 5.94/6.15  cnf(c_0_52, plain, (r1_tarski(k1_tarski(X1),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_38]), c_0_39])).
% 5.94/6.15  cnf(c_0_53, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_tarski(esk3_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_tarski(esk4_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 5.94/6.15  cnf(c_0_54, plain, (r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 5.94/6.15  cnf(c_0_55, plain, (r1_tarski(X1,k2_tarski(X3,X2))|X1!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 5.94/6.15  cnf(c_0_56, plain, (X2=X3|k1_tarski(X1)!=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 5.94/6.15  cnf(c_0_57, plain, (X1=X3|X1=X2|~r1_tarski(k1_tarski(X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_38]), c_0_39])).
% 5.94/6.15  cnf(c_0_58, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_tarski(esk4_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_tarski(esk3_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|r1_tarski(k1_tarski(esk1_0),k5_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 5.94/6.15  cnf(c_0_59, negated_conjecture, (esk1_0!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.94/6.15  cnf(c_0_60, negated_conjecture, (esk1_0!=esk3_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 5.94/6.15  cnf(c_0_61, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 5.94/6.15  cnf(c_0_62, plain, (r1_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_27, c_0_54])).
% 5.94/6.15  cnf(c_0_63, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 5.94/6.15  cnf(c_0_64, plain, (r1_tarski(X1,X2)|k4_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.94/6.15  cnf(c_0_65, plain, (r1_tarski(X1,k5_enumset1(X3,X3,X3,X3,X3,X3,X2))|X1!=k1_tarski(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_38]), c_0_39])).
% 5.94/6.15  cnf(c_0_66, plain, (X2=X3|k1_tarski(X1)!=k5_enumset1(X2,X2,X2,X2,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_38]), c_0_39])).
% 5.94/6.15  cnf(c_0_67, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_tarski(esk3_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_tarski(esk4_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60])).
% 5.94/6.15  cnf(c_0_68, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 5.94/6.15  cnf(c_0_69, plain, (X1=X2|k4_xboole_0(X2,X1)!=k1_xboole_0|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 5.94/6.15  cnf(c_0_70, plain, (r1_tarski(k1_tarski(X1),k5_enumset1(X2,X2,X2,X2,X2,X2,X1))), inference(er,[status(thm)],[c_0_65])).
% 5.94/6.15  cnf(c_0_71, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|esk2_0=esk1_0|k1_tarski(X1)!=k1_tarski(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_66])).
% 5.94/6.15  cnf(c_0_72, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 5.94/6.15  cnf(c_0_73, plain, (k2_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_68])).
% 5.94/6.15  fof(c_0_74, plain, ![X28, X29]:(k3_xboole_0(k1_tarski(X28),k1_tarski(X29))!=k1_tarski(X28)|X28=X29), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_zfmisc_1])])).
% 5.94/6.15  cnf(c_0_75, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k1_tarski(X2)|k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k1_tarski(X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 5.94/6.15  cnf(c_0_76, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk2_0)=k1_xboole_0|esk2_0=esk1_0), inference(er,[status(thm)],[c_0_71])).
% 5.94/6.15  cnf(c_0_77, plain, (r1_xboole_0(X1,k3_xboole_0(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_49])])).
% 5.94/6.15  cnf(c_0_78, plain, (X1=X2|k3_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 5.94/6.15  cnf(c_0_79, negated_conjecture, (k1_tarski(esk2_0)=k1_xboole_0|esk2_0=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_68])])).
% 5.94/6.15  cnf(c_0_80, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_77])).
% 5.94/6.15  cnf(c_0_81, negated_conjecture, (esk2_0=esk1_0|esk2_0=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])])).
% 5.94/6.15  cnf(c_0_82, negated_conjecture, (esk2_0=esk1_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_81])])).
% 5.94/6.15  cnf(c_0_83, negated_conjecture, (k1_tarski(esk4_0)=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)|k1_tarski(esk3_0)=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_82]), c_0_82]), c_0_82])).
% 5.94/6.15  cnf(c_0_84, negated_conjecture, (k1_tarski(esk3_0)=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|esk4_0=X1|esk4_0=X2|~r1_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_83])).
% 5.94/6.15  cnf(c_0_85, negated_conjecture, (k1_tarski(esk3_0)=k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)|k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_19]), c_0_59])).
% 5.94/6.15  cnf(c_0_86, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0|esk3_0=X1|esk3_0=X2|~r1_tarski(k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_57, c_0_85])).
% 5.94/6.15  cnf(c_0_87, plain, (k5_enumset1(X1,X1,X1,X1,X1,X1,X2)=k1_tarski(X1)|k4_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X2),k1_tarski(X1))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_52])).
% 5.94/6.15  cnf(c_0_88, negated_conjecture, (k5_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_19]), c_0_60])).
% 5.94/6.15  cnf(c_0_89, negated_conjecture, (k1_tarski(esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_68])])).
% 5.94/6.15  cnf(c_0_90, negated_conjecture, (esk1_0=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_89]), c_0_80])])).
% 5.94/6.15  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_90])]), ['proof']).
% 5.94/6.15  # SZS output end CNFRefutation
% 5.94/6.15  # Proof object total steps             : 92
% 5.94/6.15  # Proof object clause steps            : 63
% 5.94/6.15  # Proof object formula steps           : 29
% 5.94/6.15  # Proof object conjectures             : 23
% 5.94/6.15  # Proof object clause conjectures      : 20
% 5.94/6.15  # Proof object formula conjectures     : 3
% 5.94/6.15  # Proof object initial clauses used    : 21
% 5.94/6.15  # Proof object initial formulas used   : 14
% 5.94/6.15  # Proof object generating inferences   : 31
% 5.94/6.15  # Proof object simplifying inferences  : 40
% 5.94/6.15  # Training examples: 0 positive, 0 negative
% 5.94/6.15  # Parsed axioms                        : 14
% 5.94/6.15  # Removed by relevancy pruning/SinE    : 0
% 5.94/6.15  # Initial clauses                      : 26
% 5.94/6.15  # Removed in clause preprocessing      : 2
% 5.94/6.15  # Initial clauses in saturation        : 24
% 5.94/6.15  # Processed clauses                    : 13333
% 5.94/6.15  # ...of these trivial                  : 327
% 5.94/6.15  # ...subsumed                          : 10184
% 5.94/6.15  # ...remaining for further processing  : 2822
% 5.94/6.15  # Other redundant clauses eliminated   : 9
% 5.94/6.15  # Clauses deleted for lack of memory   : 0
% 5.94/6.15  # Backward-subsumed                    : 282
% 5.94/6.15  # Backward-rewritten                   : 354
% 5.94/6.15  # Generated clauses                    : 1104917
% 5.94/6.15  # ...of the previous two non-trivial   : 757208
% 5.94/6.15  # Contextual simplify-reflections      : 12
% 5.94/6.15  # Paramodulations                      : 1104827
% 5.94/6.15  # Factorizations                       : 72
% 5.94/6.15  # Equation resolutions                 : 18
% 5.94/6.15  # Propositional unsat checks           : 0
% 5.94/6.15  #    Propositional check models        : 0
% 5.94/6.15  #    Propositional check unsatisfiable : 0
% 5.94/6.15  #    Propositional clauses             : 0
% 5.94/6.15  #    Propositional clauses after purity: 0
% 5.94/6.15  #    Propositional unsat core size     : 0
% 5.94/6.15  #    Propositional preprocessing time  : 0.000
% 5.94/6.15  #    Propositional encoding time       : 0.000
% 5.94/6.15  #    Propositional solver time         : 0.000
% 5.94/6.15  #    Success case prop preproc time    : 0.000
% 5.94/6.15  #    Success case prop encoding time   : 0.000
% 5.94/6.15  #    Success case prop solver time     : 0.000
% 5.94/6.15  # Current number of processed clauses  : 2158
% 5.94/6.15  #    Positive orientable unit clauses  : 1472
% 5.94/6.15  #    Positive unorientable unit clauses: 1
% 5.94/6.15  #    Negative unit clauses             : 0
% 5.94/6.15  #    Non-unit-clauses                  : 685
% 5.94/6.15  # Current number of unprocessed clauses: 732286
% 5.94/6.15  # ...number of literals in the above   : 1323701
% 5.94/6.15  # Current number of archived formulas  : 0
% 5.94/6.15  # Current number of archived clauses   : 659
% 5.94/6.15  # Clause-clause subsumption calls (NU) : 419968
% 5.94/6.15  # Rec. Clause-clause subsumption calls : 316746
% 5.94/6.15  # Non-unit clause-clause subsumptions  : 10469
% 5.94/6.15  # Unit Clause-clause subsumption calls : 18716
% 5.94/6.15  # Rewrite failures with RHS unbound    : 5
% 5.94/6.15  # BW rewrite match attempts            : 59460
% 5.94/6.15  # BW rewrite match successes           : 1501
% 5.94/6.15  # Condensation attempts                : 0
% 5.94/6.15  # Condensation successes               : 0
% 5.94/6.15  # Termbank termtop insertions          : 19010582
% 5.94/6.17  
% 5.94/6.17  # -------------------------------------------------
% 5.94/6.17  # User time                : 5.529 s
% 5.94/6.17  # System time              : 0.303 s
% 5.94/6.17  # Total time               : 5.832 s
% 5.94/6.17  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
