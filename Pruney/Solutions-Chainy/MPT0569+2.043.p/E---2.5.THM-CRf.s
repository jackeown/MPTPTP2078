%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:39 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 385 expanded)
%              Number of clauses        :   52 ( 175 expanded)
%              Number of leaves         :   13 (  91 expanded)
%              Depth                    :   14
%              Number of atoms          :  198 (1387 expanded)
%              Number of equality atoms :   25 ( 177 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

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

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( k10_relat_1(esk6_0,esk5_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) )
    & ( k10_relat_1(esk6_0,esk5_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X12] :
      ( X12 = k1_xboole_0
      | r2_hidden(esk2_1(X12),X12) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_16,plain,(
    ! [X38,X39,X40,X42] :
      ( ( r2_hidden(esk4_3(X38,X39,X40),k2_relat_1(X40))
        | ~ r2_hidden(X38,k10_relat_1(X40,X39))
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(k4_tarski(X38,esk4_3(X38,X39,X40)),X40)
        | ~ r2_hidden(X38,k10_relat_1(X40,X39))
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(esk4_3(X38,X39,X40),X39)
        | ~ r2_hidden(X38,k10_relat_1(X40,X39))
        | ~ v1_relat_1(X40) )
      & ( ~ r2_hidden(X42,k2_relat_1(X40))
        | ~ r2_hidden(k4_tarski(X38,X42),X40)
        | ~ r2_hidden(X42,X39)
        | r2_hidden(X38,k10_relat_1(X40,X39))
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_17,negated_conjecture,
    ( k10_relat_1(esk6_0,esk5_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | ~ r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X32,X33,X34,X36] :
      ( ( r2_hidden(esk3_3(X32,X33,X34),k1_relat_1(X34))
        | ~ r2_hidden(X32,k9_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(k4_tarski(esk3_3(X32,X33,X34),X32),X34)
        | ~ r2_hidden(X32,k9_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( r2_hidden(esk3_3(X32,X33,X34),X33)
        | ~ r2_hidden(X32,k9_relat_1(X34,X33))
        | ~ v1_relat_1(X34) )
      & ( ~ r2_hidden(X36,k1_relat_1(X34))
        | ~ r2_hidden(k4_tarski(X36,X32),X34)
        | ~ r2_hidden(X36,X33)
        | r2_hidden(X32,k9_relat_1(X34,X33))
        | ~ v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_25,plain,(
    ! [X37] :
      ( ~ v1_relat_1(X37)
      | k9_relat_1(X37,k1_relat_1(X37)) = k2_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk6_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k10_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_30,plain,(
    ! [X43,X44,X45] :
      ( ( r2_hidden(X43,k1_relat_1(X45))
        | ~ r2_hidden(k4_tarski(X43,X44),X45)
        | ~ v1_relat_1(X45) )
      & ( r2_hidden(X44,k2_relat_1(X45))
        | ~ r2_hidden(k4_tarski(X43,X44),X45)
        | ~ v1_relat_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk4_3(X1,X2,esk6_0),X2)
    | ~ r2_hidden(X1,k10_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k9_relat_1(esk6_0,X2)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( k9_relat_1(esk6_0,k1_relat_1(esk6_0)) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk6_0))
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_36])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(X1,k1_relat_1(esk6_0),esk6_0),X1),esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_43])).

fof(c_0_49,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_xboole_0(k2_tarski(X29,X30),X31)
      | ~ r2_hidden(X29,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_50,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_51,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_52,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_53,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(esk6_0,X2))
    | ~ r2_hidden(k4_tarski(X1,X3),esk6_0)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),esk1_2(k2_relat_1(esk6_0),esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)
    | r2_hidden(esk1_2(X1,esk5_0),esk5_0)
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_43])).

cnf(c_0_58,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_63,plain,(
    ! [X14] : r1_xboole_0(X14,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,X1))
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k10_relat_1(esk6_0,esk5_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),X1)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))
    | r2_hidden(esk1_2(esk5_0,X1),esk5_0)
    | ~ r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_42])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),esk5_0)
    | ~ r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_46])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_34]),c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:10:25 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.48/0.64  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.48/0.64  # and selection function SelectNegativeLiterals.
% 0.48/0.64  #
% 0.48/0.64  # Preprocessing time       : 0.028 s
% 0.48/0.64  # Presaturation interreduction done
% 0.48/0.64  
% 0.48/0.64  # Proof found!
% 0.48/0.64  # SZS status Theorem
% 0.48/0.64  # SZS output start CNFRefutation
% 0.48/0.64  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.48/0.64  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.48/0.64  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.48/0.64  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.48/0.64  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.48/0.64  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.48/0.64  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.48/0.64  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.48/0.64  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.48/0.64  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.48/0.64  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.48/0.64  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.48/0.64  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.48/0.64  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.48/0.64  fof(c_0_14, negated_conjecture, (v1_relat_1(esk6_0)&((k10_relat_1(esk6_0,esk5_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0))&(k10_relat_1(esk6_0,esk5_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk6_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.48/0.64  fof(c_0_15, plain, ![X12]:(X12=k1_xboole_0|r2_hidden(esk2_1(X12),X12)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.48/0.64  fof(c_0_16, plain, ![X38, X39, X40, X42]:((((r2_hidden(esk4_3(X38,X39,X40),k2_relat_1(X40))|~r2_hidden(X38,k10_relat_1(X40,X39))|~v1_relat_1(X40))&(r2_hidden(k4_tarski(X38,esk4_3(X38,X39,X40)),X40)|~r2_hidden(X38,k10_relat_1(X40,X39))|~v1_relat_1(X40)))&(r2_hidden(esk4_3(X38,X39,X40),X39)|~r2_hidden(X38,k10_relat_1(X40,X39))|~v1_relat_1(X40)))&(~r2_hidden(X42,k2_relat_1(X40))|~r2_hidden(k4_tarski(X38,X42),X40)|~r2_hidden(X42,X39)|r2_hidden(X38,k10_relat_1(X40,X39))|~v1_relat_1(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.48/0.64  cnf(c_0_17, negated_conjecture, (k10_relat_1(esk6_0,esk5_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.64  cnf(c_0_18, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.48/0.64  fof(c_0_19, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.48/0.64  cnf(c_0_20, plain, (r2_hidden(esk4_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.64  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.64  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|~r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.48/0.64  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.64  fof(c_0_24, plain, ![X32, X33, X34, X36]:((((r2_hidden(esk3_3(X32,X33,X34),k1_relat_1(X34))|~r2_hidden(X32,k9_relat_1(X34,X33))|~v1_relat_1(X34))&(r2_hidden(k4_tarski(esk3_3(X32,X33,X34),X32),X34)|~r2_hidden(X32,k9_relat_1(X34,X33))|~v1_relat_1(X34)))&(r2_hidden(esk3_3(X32,X33,X34),X33)|~r2_hidden(X32,k9_relat_1(X34,X33))|~v1_relat_1(X34)))&(~r2_hidden(X36,k1_relat_1(X34))|~r2_hidden(k4_tarski(X36,X32),X34)|~r2_hidden(X36,X33)|r2_hidden(X32,k9_relat_1(X34,X33))|~v1_relat_1(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.48/0.64  fof(c_0_25, plain, ![X37]:(~v1_relat_1(X37)|k9_relat_1(X37,k1_relat_1(X37))=k2_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.48/0.64  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.64  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk6_0),k2_relat_1(esk6_0))|~r2_hidden(X1,k10_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.48/0.64  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.48/0.64  cnf(c_0_29, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.64  fof(c_0_30, plain, ![X43, X44, X45]:((r2_hidden(X43,k1_relat_1(X45))|~r2_hidden(k4_tarski(X43,X44),X45)|~v1_relat_1(X45))&(r2_hidden(X44,k2_relat_1(X45))|~r2_hidden(k4_tarski(X43,X44),X45)|~v1_relat_1(X45))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.48/0.64  cnf(c_0_31, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.48/0.64  cnf(c_0_32, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.48/0.64  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.48/0.64  cnf(c_0_34, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.48/0.64  cnf(c_0_35, negated_conjecture, (r2_hidden(esk4_3(X1,X2,esk6_0),X2)|~r2_hidden(X1,k10_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_29, c_0_21])).
% 0.48/0.64  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.48/0.64  cnf(c_0_37, plain, (r2_hidden(X3,k10_relat_1(X2,X4))|~r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,X4)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.48/0.64  cnf(c_0_38, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.48/0.64  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(X1,X2,esk6_0),X1),esk6_0)|~r2_hidden(X1,k9_relat_1(esk6_0,X2))), inference(spm,[status(thm)],[c_0_31, c_0_21])).
% 0.48/0.64  cnf(c_0_40, negated_conjecture, (k9_relat_1(esk6_0,k1_relat_1(esk6_0))=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.48/0.64  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),X1),k2_relat_1(esk6_0))|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.48/0.64  cnf(c_0_42, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_35, c_0_28])).
% 0.48/0.64  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_1(k10_relat_1(esk6_0,esk5_0)),k10_relat_1(esk6_0,esk5_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_36])).
% 0.48/0.64  cnf(c_0_44, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_37, c_0_38])).
% 0.48/0.64  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(X1,k1_relat_1(esk6_0),esk6_0),X1),esk6_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.48/0.64  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.48/0.64  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X2)|~r2_hidden(X3,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_26, c_0_36])).
% 0.48/0.64  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),esk5_0)|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_43])).
% 0.48/0.64  fof(c_0_49, plain, ![X29, X30, X31]:(~r1_xboole_0(k2_tarski(X29,X30),X31)|~r2_hidden(X29,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.48/0.64  fof(c_0_50, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.48/0.64  fof(c_0_51, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.48/0.64  fof(c_0_52, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.48/0.64  fof(c_0_53, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.48/0.64  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,k10_relat_1(esk6_0,X2))|~r2_hidden(k4_tarski(X1,X3),esk6_0)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_44, c_0_21])).
% 0.48/0.64  cnf(c_0_55, negated_conjecture, (r2_hidden(k4_tarski(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),esk1_2(k2_relat_1(esk6_0),esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.48/0.64  cnf(c_0_56, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)|r2_hidden(esk1_2(X1,esk5_0),esk5_0)|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.48/0.64  cnf(c_0_57, negated_conjecture, (r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_43])).
% 0.48/0.64  cnf(c_0_58, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.48/0.64  cnf(c_0_59, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.48/0.64  cnf(c_0_60, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.48/0.64  cnf(c_0_61, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.48/0.64  cnf(c_0_62, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.48/0.64  fof(c_0_63, plain, ![X14]:r1_xboole_0(X14,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.48/0.64  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,X1))|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.48/0.64  cnf(c_0_65, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),esk5_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.48/0.64  cnf(c_0_66, plain, (~r2_hidden(X1,X3)|~r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X2),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_61]), c_0_62])).
% 0.48/0.64  cnf(c_0_67, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.48/0.64  cnf(c_0_68, negated_conjecture, (r2_hidden(esk3_3(esk1_2(k2_relat_1(esk6_0),esk5_0),k1_relat_1(esk6_0),esk6_0),k10_relat_1(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.48/0.64  cnf(c_0_69, negated_conjecture, (k10_relat_1(esk6_0,esk5_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.48/0.64  cnf(c_0_70, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.48/0.64  cnf(c_0_71, negated_conjecture, (r1_xboole_0(k2_relat_1(esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.48/0.64  cnf(c_0_72, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),X1)|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_47, c_0_65])).
% 0.48/0.64  cnf(c_0_73, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),k2_relat_1(esk6_0))|r2_hidden(esk1_2(esk5_0,X1),esk5_0)|~r2_hidden(esk4_3(esk2_1(k10_relat_1(esk6_0,esk5_0)),esk5_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_42])).
% 0.48/0.64  cnf(c_0_74, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),esk5_0)|~r2_hidden(esk1_2(k2_relat_1(esk6_0),esk5_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_65])).
% 0.48/0.64  cnf(c_0_75, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk6_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_71])).
% 0.48/0.64  cnf(c_0_76, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_72, c_0_46])).
% 0.48/0.64  cnf(c_0_77, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k2_relat_1(esk6_0)),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_34]), c_0_74])).
% 0.48/0.64  cnf(c_0_78, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])]), ['proof']).
% 0.48/0.64  # SZS output end CNFRefutation
% 0.48/0.64  # Proof object total steps             : 79
% 0.48/0.64  # Proof object clause steps            : 52
% 0.48/0.64  # Proof object formula steps           : 27
% 0.48/0.64  # Proof object conjectures             : 34
% 0.48/0.64  # Proof object clause conjectures      : 31
% 0.48/0.64  # Proof object formula conjectures     : 3
% 0.48/0.64  # Proof object initial clauses used    : 19
% 0.48/0.64  # Proof object initial formulas used   : 13
% 0.48/0.64  # Proof object generating inferences   : 31
% 0.48/0.64  # Proof object simplifying inferences  : 9
% 0.48/0.64  # Training examples: 0 positive, 0 negative
% 0.48/0.64  # Parsed axioms                        : 13
% 0.48/0.64  # Removed by relevancy pruning/SinE    : 0
% 0.48/0.64  # Initial clauses                      : 24
% 0.48/0.64  # Removed in clause preprocessing      : 4
% 0.48/0.64  # Initial clauses in saturation        : 20
% 0.48/0.64  # Processed clauses                    : 1952
% 0.48/0.64  # ...of these trivial                  : 86
% 0.48/0.64  # ...subsumed                          : 969
% 0.48/0.64  # ...remaining for further processing  : 897
% 0.48/0.64  # Other redundant clauses eliminated   : 18
% 0.48/0.64  # Clauses deleted for lack of memory   : 0
% 0.48/0.64  # Backward-subsumed                    : 18
% 0.48/0.64  # Backward-rewritten                   : 99
% 0.48/0.64  # Generated clauses                    : 30220
% 0.48/0.64  # ...of the previous two non-trivial   : 14074
% 0.48/0.64  # Contextual simplify-reflections      : 8
% 0.48/0.64  # Paramodulations                      : 30186
% 0.48/0.64  # Factorizations                       : 16
% 0.48/0.64  # Equation resolutions                 : 18
% 0.48/0.64  # Propositional unsat checks           : 0
% 0.48/0.64  #    Propositional check models        : 0
% 0.48/0.64  #    Propositional check unsatisfiable : 0
% 0.48/0.64  #    Propositional clauses             : 0
% 0.48/0.64  #    Propositional clauses after purity: 0
% 0.48/0.64  #    Propositional unsat core size     : 0
% 0.48/0.64  #    Propositional preprocessing time  : 0.000
% 0.48/0.64  #    Propositional encoding time       : 0.000
% 0.48/0.64  #    Propositional solver time         : 0.000
% 0.48/0.64  #    Success case prop preproc time    : 0.000
% 0.48/0.64  #    Success case prop encoding time   : 0.000
% 0.48/0.64  #    Success case prop solver time     : 0.000
% 0.48/0.64  # Current number of processed clauses  : 760
% 0.48/0.64  #    Positive orientable unit clauses  : 122
% 0.48/0.64  #    Positive unorientable unit clauses: 0
% 0.48/0.64  #    Negative unit clauses             : 2
% 0.48/0.64  #    Non-unit-clauses                  : 636
% 0.48/0.64  # Current number of unprocessed clauses: 11704
% 0.48/0.64  # ...number of literals in the above   : 42837
% 0.48/0.64  # Current number of archived formulas  : 0
% 0.48/0.64  # Current number of archived clauses   : 141
% 0.48/0.64  # Clause-clause subsumption calls (NU) : 49257
% 0.48/0.64  # Rec. Clause-clause subsumption calls : 39668
% 0.48/0.64  # Non-unit clause-clause subsumptions  : 760
% 0.48/0.64  # Unit Clause-clause subsumption calls : 524
% 0.48/0.64  # Rewrite failures with RHS unbound    : 0
% 0.48/0.64  # BW rewrite match attempts            : 133
% 0.48/0.64  # BW rewrite match successes           : 8
% 0.48/0.64  # Condensation attempts                : 0
% 0.48/0.64  # Condensation successes               : 0
% 0.48/0.64  # Termbank termtop insertions          : 704284
% 0.48/0.64  
% 0.48/0.64  # -------------------------------------------------
% 0.48/0.64  # User time                : 0.286 s
% 0.48/0.64  # System time              : 0.013 s
% 0.48/0.64  # Total time               : 0.299 s
% 0.48/0.64  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
