%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:51 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 317 expanded)
%              Number of clauses        :   51 ( 123 expanded)
%              Number of leaves         :   20 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  193 ( 553 expanded)
%              Number of equality atoms :   96 ( 358 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(t47_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
           => k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_21,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X42)
      | ~ v1_relat_1(X43)
      | ~ r1_tarski(k1_relat_1(X42),k2_relat_1(X43))
      | k2_relat_1(k5_relat_1(X43,X42)) = k2_relat_1(X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & k1_relat_1(esk3_0) = k1_tarski(esk2_0)
    & k2_relat_1(esk3_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_23,plain,(
    ! [X46,X47] :
      ( ~ v1_relat_1(X47)
      | k7_relat_1(X47,X46) = k5_relat_1(k6_relat_1(X46),X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_24,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X38)
      | k2_relat_1(k7_relat_1(X38,X37)) = k9_relat_1(X38,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_25,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_29,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_30,plain,(
    ! [X24,X25,X26,X27,X28,X29] : k5_enumset1(X24,X24,X25,X26,X27,X28,X29) = k4_enumset1(X24,X25,X26,X27,X28,X29) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_31,plain,(
    ! [X31,X32] :
      ( ( r2_hidden(esk1_2(X31,X32),X31)
        | X31 = k1_tarski(X32)
        | X31 = k1_xboole_0 )
      & ( esk1_2(X31,X32) != X32
        | X31 = k1_tarski(X32)
        | X31 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

fof(c_0_32,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X34)
      | k11_relat_1(X34,X35) = k9_relat_1(X34,k1_tarski(X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_33,plain,
    ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_35,plain,(
    ! [X36] : v1_relat_1(k6_relat_1(X36)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_36,plain,(
    ! [X45] :
      ( k1_relat_1(k6_relat_1(X45)) = X45
      & k2_relat_1(k6_relat_1(X45)) = X45 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_37,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_39,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk3_0) != k1_tarski(k1_funct_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_48,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(k5_relat_1(X1,esk3_0)) = k2_relat_1(esk3_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(esk3_0),k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_50,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_51,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk3_0) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_34])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_55,plain,(
    ! [X30] : ~ v1_xboole_0(k1_tarski(X30)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(esk3_0) != k5_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

fof(c_0_58,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r2_hidden(k4_tarski(X39,X40),X41)
        | r2_hidden(X40,k11_relat_1(X41,X39))
        | ~ v1_relat_1(X41) )
      & ( ~ r2_hidden(X40,k11_relat_1(X41,X39))
        | r2_hidden(k4_tarski(X39,X40),X41)
        | ~ v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_59,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( k9_relat_1(esk3_0,X1) = k2_relat_1(esk3_0)
    | ~ r1_tarski(k1_relat_1(esk3_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_64,plain,(
    ! [X44] :
      ( ( k1_relat_1(X44) != k1_xboole_0
        | k2_relat_1(X44) = k1_xboole_0
        | ~ v1_relat_1(X44) )
      & ( k2_relat_1(X44) != k1_xboole_0
        | k1_relat_1(X44) = k1_xboole_0
        | ~ v1_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_funct_1(esk3_0,esk2_0)),X1)
    | X1 != k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k9_relat_1(esk3_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( k1_relat_1(esk3_0) = k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_69,negated_conjecture,
    ( k9_relat_1(esk3_0,k1_relat_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,plain,
    ( ~ v1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_71,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( k2_relat_1(esk3_0) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)),k2_relat_1(esk3_0)) ),
    inference(er,[status(thm)],[c_0_65])).

fof(c_0_73,plain,(
    ! [X48,X49,X50] :
      ( ( r2_hidden(X48,k1_relat_1(X50))
        | ~ r2_hidden(k4_tarski(X48,X49),X50)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( X49 = k1_funct_1(X50,X48)
        | ~ r2_hidden(k4_tarski(X48,X49),X50)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) )
      & ( ~ r2_hidden(X48,k1_relat_1(X50))
        | X49 != k1_funct_1(X50,X48)
        | r2_hidden(k4_tarski(X48,X49),X50)
        | ~ v1_relat_1(X50)
        | ~ v1_funct_1(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk3_0)
    | ~ r2_hidden(X2,k11_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( k11_relat_1(esk3_0,esk2_0) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_34])])).

cnf(c_0_78,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_79,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,X1),esk3_0)
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_83,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_84,negated_conjecture,
    ( X1 = k1_funct_1(esk3_0,X2)
    | ~ r2_hidden(k4_tarski(X2,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_34])])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_87,negated_conjecture,
    ( esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)) = k1_funct_1(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_56])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_88]),c_0_34])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_89]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:41:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S002A
% 0.12/0.38  # and selection function SelectNegativeLiterals.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.12/0.38  fof(t47_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X1),k2_relat_1(X2))=>k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 0.12/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.12/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.12/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.12/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.12/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.12/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.12/0.38  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.12/0.38  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.12/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.12/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.12/0.38  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.12/0.38  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.12/0.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.12/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.38  fof(c_0_20, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.12/0.38  fof(c_0_21, plain, ![X42, X43]:(~v1_relat_1(X42)|(~v1_relat_1(X43)|(~r1_tarski(k1_relat_1(X42),k2_relat_1(X43))|k2_relat_1(k5_relat_1(X43,X42))=k2_relat_1(X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).
% 0.12/0.38  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(k1_relat_1(esk3_0)=k1_tarski(esk2_0)&k2_relat_1(esk3_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.12/0.38  fof(c_0_23, plain, ![X46, X47]:(~v1_relat_1(X47)|k7_relat_1(X47,X46)=k5_relat_1(k6_relat_1(X46),X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.12/0.38  fof(c_0_24, plain, ![X37, X38]:(~v1_relat_1(X38)|k2_relat_1(k7_relat_1(X38,X37))=k9_relat_1(X38,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.12/0.38  fof(c_0_25, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.12/0.38  fof(c_0_26, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  fof(c_0_27, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.12/0.38  fof(c_0_28, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.12/0.38  fof(c_0_29, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.12/0.38  fof(c_0_30, plain, ![X24, X25, X26, X27, X28, X29]:k5_enumset1(X24,X24,X25,X26,X27,X28,X29)=k4_enumset1(X24,X25,X26,X27,X28,X29), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.12/0.38  fof(c_0_31, plain, ![X31, X32]:((r2_hidden(esk1_2(X31,X32),X31)|(X31=k1_tarski(X32)|X31=k1_xboole_0))&(esk1_2(X31,X32)!=X32|(X31=k1_tarski(X32)|X31=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.12/0.38  fof(c_0_32, plain, ![X34, X35]:(~v1_relat_1(X34)|k11_relat_1(X34,X35)=k9_relat_1(X34,k1_tarski(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.12/0.38  cnf(c_0_33, plain, (k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k2_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  fof(c_0_35, plain, ![X36]:v1_relat_1(k6_relat_1(X36)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.12/0.38  fof(c_0_36, plain, ![X45]:(k1_relat_1(k6_relat_1(X45))=X45&k2_relat_1(k6_relat_1(X45))=X45), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.12/0.38  cnf(c_0_37, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.38  cnf(c_0_38, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.38  fof(c_0_39, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (k2_relat_1(esk3_0)!=k1_tarski(k1_funct_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.38  cnf(c_0_43, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.38  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_45, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.38  cnf(c_0_46, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.38  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_48, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (k2_relat_1(k5_relat_1(X1,esk3_0))=k2_relat_1(esk3_0)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(esk3_0),k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.38  cnf(c_0_50, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.38  cnf(c_0_51, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.38  cnf(c_0_52, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk3_0)=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.12/0.38  cnf(c_0_53, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_34])).
% 0.12/0.38  cnf(c_0_54, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  fof(c_0_55, plain, ![X30]:~v1_xboole_0(k1_tarski(X30)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.12/0.38  cnf(c_0_56, negated_conjecture, (k2_relat_1(esk3_0)!=k5_enumset1(k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0),k1_funct_1(esk3_0,esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.12/0.38  cnf(c_0_57, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.12/0.38  fof(c_0_58, plain, ![X39, X40, X41]:((~r2_hidden(k4_tarski(X39,X40),X41)|r2_hidden(X40,k11_relat_1(X41,X39))|~v1_relat_1(X41))&(~r2_hidden(X40,k11_relat_1(X41,X39))|r2_hidden(k4_tarski(X39,X40),X41)|~v1_relat_1(X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.12/0.38  cnf(c_0_59, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (k1_relat_1(esk3_0)=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_61, negated_conjecture, (k9_relat_1(esk3_0,X1)=k2_relat_1(esk3_0)|~r1_tarski(k1_relat_1(esk3_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_53])).
% 0.12/0.38  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_54])).
% 0.12/0.38  cnf(c_0_63, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.12/0.38  fof(c_0_64, plain, ![X44]:((k1_relat_1(X44)!=k1_xboole_0|k2_relat_1(X44)=k1_xboole_0|~v1_relat_1(X44))&(k2_relat_1(X44)!=k1_xboole_0|k1_relat_1(X44)=k1_xboole_0|~v1_relat_1(X44))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.12/0.38  cnf(c_0_65, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_funct_1(esk3_0,esk2_0)),X1)|X1!=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.12/0.38  cnf(c_0_66, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (k9_relat_1(esk3_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))=k11_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_34])).
% 0.12/0.38  cnf(c_0_68, negated_conjecture, (k1_relat_1(esk3_0)=k5_enumset1(esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0,esk2_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (k9_relat_1(esk3_0,k1_relat_1(esk3_0))=k2_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.38  cnf(c_0_70, plain, (~v1_xboole_0(k5_enumset1(X1,X1,X1,X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.12/0.38  cnf(c_0_71, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.12/0.38  cnf(c_0_72, negated_conjecture, (k2_relat_1(esk3_0)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)),k2_relat_1(esk3_0))), inference(er,[status(thm)],[c_0_65])).
% 0.12/0.38  fof(c_0_73, plain, ![X48, X49, X50]:(((r2_hidden(X48,k1_relat_1(X50))|~r2_hidden(k4_tarski(X48,X49),X50)|(~v1_relat_1(X50)|~v1_funct_1(X50)))&(X49=k1_funct_1(X50,X48)|~r2_hidden(k4_tarski(X48,X49),X50)|(~v1_relat_1(X50)|~v1_funct_1(X50))))&(~r2_hidden(X48,k1_relat_1(X50))|X49!=k1_funct_1(X50,X48)|r2_hidden(k4_tarski(X48,X49),X50)|(~v1_relat_1(X50)|~v1_funct_1(X50)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.12/0.38  cnf(c_0_74, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk3_0)|~r2_hidden(X2,k11_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_66, c_0_34])).
% 0.12/0.38  cnf(c_0_75, negated_conjecture, (k11_relat_1(esk3_0,esk2_0)=k2_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_70, c_0_68])).
% 0.12/0.38  cnf(c_0_77, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_34])])).
% 0.12/0.38  cnf(c_0_78, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.38  cnf(c_0_79, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.12/0.38  cnf(c_0_80, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_81, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,X1),esk3_0)|~r2_hidden(X1,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.12/0.38  cnf(c_0_82, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0)),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 0.12/0.38  cnf(c_0_83, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_84, negated_conjecture, (X1=k1_funct_1(esk3_0,X2)|~r2_hidden(k4_tarski(X2,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_34])])).
% 0.12/0.38  cnf(c_0_85, negated_conjecture, (r2_hidden(k4_tarski(esk2_0,esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0))),esk3_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.12/0.38  cnf(c_0_86, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.12/0.38  cnf(c_0_87, negated_conjecture, (esk1_2(k2_relat_1(esk3_0),k1_funct_1(esk3_0,esk2_0))=k1_funct_1(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.12/0.38  cnf(c_0_88, negated_conjecture, (k2_relat_1(esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_56])).
% 0.12/0.38  cnf(c_0_89, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_88]), c_0_34])])).
% 0.12/0.38  cnf(c_0_90, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_89]), c_0_78])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 91
% 0.12/0.38  # Proof object clause steps            : 51
% 0.12/0.38  # Proof object formula steps           : 40
% 0.12/0.38  # Proof object conjectures             : 29
% 0.12/0.38  # Proof object clause conjectures      : 26
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 24
% 0.12/0.38  # Proof object initial formulas used   : 20
% 0.12/0.38  # Proof object generating inferences   : 19
% 0.12/0.38  # Proof object simplifying inferences  : 53
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 20
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 31
% 0.12/0.38  # Removed in clause preprocessing      : 6
% 0.12/0.38  # Initial clauses in saturation        : 25
% 0.12/0.38  # Processed clauses                    : 121
% 0.12/0.38  # ...of these trivial                  : 1
% 0.12/0.38  # ...subsumed                          : 15
% 0.12/0.38  # ...remaining for further processing  : 105
% 0.12/0.38  # Other redundant clauses eliminated   : 2
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 1
% 0.12/0.38  # Backward-rewritten                   : 32
% 0.12/0.38  # Generated clauses                    : 405
% 0.12/0.38  # ...of the previous two non-trivial   : 416
% 0.12/0.38  # Contextual simplify-reflections      : 0
% 0.12/0.38  # Paramodulations                      : 396
% 0.12/0.38  # Factorizations                       : 4
% 0.12/0.38  # Equation resolutions                 : 5
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 46
% 0.12/0.38  #    Positive orientable unit clauses  : 16
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 29
% 0.12/0.38  # Current number of unprocessed clauses: 336
% 0.12/0.38  # ...number of literals in the above   : 1317
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 63
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 213
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 122
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.12/0.38  # Unit Clause-clause subsumption calls : 106
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 9
% 0.12/0.38  # BW rewrite match successes           : 4
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 7710
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.037 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.043 s
% 0.12/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
