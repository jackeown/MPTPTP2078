%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 334 expanded)
%              Number of clauses        :   55 ( 149 expanded)
%              Number of leaves         :   14 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  159 ( 718 expanded)
%              Number of equality atoms :   25 ( 167 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t149_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
        & r2_hidden(X4,X3)
        & r1_xboole_0(X3,X2) )
     => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

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

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(t74_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( ~ r1_xboole_0(X1,k3_xboole_0(X2,X3))
        & r1_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))
          & r2_hidden(X4,X3)
          & r1_xboole_0(X3,X2) )
       => r1_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    inference(assume_negation,[status(cth)],[t149_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_xboole_0(X9,X10) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | r1_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_16,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))
    & r2_hidden(esk6_0,esk5_0)
    & r1_xboole_0(esk5_0,esk4_0)
    & ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X39,X40] :
      ( r2_hidden(X39,X40)
      | r1_xboole_0(k1_tarski(X39),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_18,plain,(
    ! [X36] : k2_tarski(X36,X36) = k1_tarski(X36) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X37,X38] : k1_enumset1(X37,X37,X38) = k2_tarski(X37,X38) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( ~ r1_xboole_0(X7,X8)
      | r1_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_26,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r1_xboole_0(X15,X16)
        | r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)) )
      & ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_27,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_28,plain,(
    ! [X34,X35] :
      ( ( ~ r1_xboole_0(X34,X35)
        | k4_xboole_0(X34,X35) = X34 )
      & ( k4_xboole_0(X34,X35) != X34
        | r1_xboole_0(X34,X35) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk6_0,X1)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_enumset1(X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_xboole_0(k1_enumset1(esk6_0,esk6_0,esk6_0),X1)
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_38,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_39,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk4_0) = esk5_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

fof(c_0_41,plain,(
    ! [X21,X22,X23] :
      ( ( r1_tarski(X21,X22)
        | ~ r1_tarski(X21,k4_xboole_0(X22,X23)) )
      & ( r1_xboole_0(X21,X23)
        | ~ r1_tarski(X21,k4_xboole_0(X22,X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_42,negated_conjecture,
    ( r1_xboole_0(k1_enumset1(esk6_0,esk6_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_32])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(esk6_0,esk6_0,esk6_0),esk4_0) = k1_enumset1(esk6_0,esk6_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k1_enumset1(esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_23]),c_0_24]),c_0_34])).

cnf(c_0_50,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_34]),c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( r1_xboole_0(X1,k4_xboole_0(esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_xboole_0(X1,esk4_0)
    | ~ r1_tarski(X1,k1_enumset1(esk6_0,esk6_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),k1_enumset1(esk6_0,esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk5_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_51])).

fof(c_0_55,plain,(
    ! [X29,X30,X31] :
      ( r1_xboole_0(X29,k3_xboole_0(X30,X31))
      | ~ r1_xboole_0(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(esk5_0,esk5_0),X1) = k4_xboole_0(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(esk5_0,esk5_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_35,c_0_51])).

cnf(c_0_59,plain,
    ( r1_xboole_0(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_60,plain,(
    ! [X32,X33] : r1_xboole_0(k4_xboole_0(X32,X33),X33) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_61,plain,(
    ! [X26,X27,X28] :
      ( ( r1_xboole_0(X26,k2_xboole_0(X27,X28))
        | ~ r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,X28) )
      & ( r1_xboole_0(X26,X27)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) )
      & ( r1_xboole_0(X26,X28)
        | ~ r1_xboole_0(X26,k2_xboole_0(X27,X28)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( r1_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk5_0) = k4_xboole_0(X1,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_57]),c_0_58])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_59,c_0_34])).

cnf(c_0_66,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_68,plain,
    ( r1_xboole_0(X1,k2_xboole_0(X2,X3))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_50])).

cnf(c_0_70,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X2)) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_64])).

cnf(c_0_72,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_34])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0))
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_37])).

cnf(c_0_75,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_64]),c_0_71]),c_0_72])])).

cnf(c_0_77,plain,
    ( r2_hidden(esk2_2(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))
    | r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_50])).

cnf(c_0_78,negated_conjecture,
    ( r1_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(X1,esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,esk4_0),esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03EI
% 0.20/0.42  # and selection function SelectLComplex.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t149_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 0.20/0.42  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.42  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.20/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.42  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.20/0.42  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.20/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.42  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.20/0.42  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.20/0.42  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.20/0.42  fof(t74_xboole_1, axiom, ![X1, X2, X3]:~((~(r1_xboole_0(X1,k3_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 0.20/0.42  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.20/0.42  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.42  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(((r1_tarski(k3_xboole_0(X1,X2),k1_tarski(X4))&r2_hidden(X4,X3))&r1_xboole_0(X3,X2))=>r1_xboole_0(k2_xboole_0(X1,X3),X2))), inference(assume_negation,[status(cth)],[t149_zfmisc_1])).
% 0.20/0.42  fof(c_0_15, plain, ![X9, X10, X12, X13, X14]:(((r2_hidden(esk1_2(X9,X10),X9)|r1_xboole_0(X9,X10))&(r2_hidden(esk1_2(X9,X10),X10)|r1_xboole_0(X9,X10)))&(~r2_hidden(X14,X12)|~r2_hidden(X14,X13)|~r1_xboole_0(X12,X13))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.42  fof(c_0_16, negated_conjecture, (((r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))&r2_hidden(esk6_0,esk5_0))&r1_xboole_0(esk5_0,esk4_0))&~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.42  fof(c_0_17, plain, ![X39, X40]:(r2_hidden(X39,X40)|r1_xboole_0(k1_tarski(X39),X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.20/0.42  fof(c_0_18, plain, ![X36]:k2_tarski(X36,X36)=k1_tarski(X36), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.42  fof(c_0_19, plain, ![X37, X38]:k1_enumset1(X37,X37,X38)=k2_tarski(X37,X38), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.42  cnf(c_0_20, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_21, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_22, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.42  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.42  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  fof(c_0_25, plain, ![X7, X8]:(~r1_xboole_0(X7,X8)|r1_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.20/0.42  fof(c_0_26, plain, ![X15, X16, X18, X19, X20]:((r1_xboole_0(X15,X16)|r2_hidden(esk2_2(X15,X16),k3_xboole_0(X15,X16)))&(~r2_hidden(X20,k3_xboole_0(X18,X19))|~r1_xboole_0(X18,X19))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.20/0.42  fof(c_0_27, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.42  fof(c_0_28, plain, ![X34, X35]:((~r1_xboole_0(X34,X35)|k4_xboole_0(X34,X35)=X34)&(k4_xboole_0(X34,X35)!=X34|r1_xboole_0(X34,X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk6_0,X1)|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.42  cnf(c_0_30, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_enumset1(X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.20/0.42  cnf(c_0_31, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (r1_xboole_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_33, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_34, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.42  cnf(c_0_35, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, (r1_xboole_0(k1_enumset1(esk6_0,esk6_0,esk6_0),X1)|~r1_xboole_0(X1,esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.42  cnf(c_0_37, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.42  fof(c_0_38, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.20/0.42  cnf(c_0_39, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.42  cnf(c_0_40, negated_conjecture, (k4_xboole_0(esk5_0,esk4_0)=esk5_0), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.20/0.42  fof(c_0_41, plain, ![X21, X22, X23]:((r1_tarski(X21,X22)|~r1_tarski(X21,k4_xboole_0(X22,X23)))&(r1_xboole_0(X21,X23)|~r1_tarski(X21,k4_xboole_0(X22,X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.20/0.42  cnf(c_0_42, negated_conjecture, (r1_xboole_0(k1_enumset1(esk6_0,esk6_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.42  cnf(c_0_43, negated_conjecture, (r1_tarski(k3_xboole_0(esk3_0,esk4_0),k1_tarski(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_44, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.42  cnf(c_0_45, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_32])])).
% 0.20/0.42  cnf(c_0_46, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.42  cnf(c_0_47, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.42  cnf(c_0_48, negated_conjecture, (k4_xboole_0(k1_enumset1(esk6_0,esk6_0,esk6_0),esk4_0)=k1_enumset1(esk6_0,esk6_0,esk6_0)), inference(spm,[status(thm)],[c_0_35, c_0_42])).
% 0.20/0.42  cnf(c_0_49, negated_conjecture, (r1_tarski(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k1_enumset1(esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_23]), c_0_24]), c_0_34])).
% 0.20/0.42  cnf(c_0_50, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_34]), c_0_34])).
% 0.20/0.42  cnf(c_0_51, negated_conjecture, (r1_xboole_0(X1,k4_xboole_0(esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.42  cnf(c_0_52, negated_conjecture, (r1_xboole_0(X1,esk4_0)|~r1_tarski(X1,k1_enumset1(esk6_0,esk6_0,esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.42  cnf(c_0_53, negated_conjecture, (r1_tarski(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),k1_enumset1(esk6_0,esk6_0,esk6_0))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.42  cnf(c_0_54, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk5_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_31, c_0_51])).
% 0.20/0.42  fof(c_0_55, plain, ![X29, X30, X31]:(r1_xboole_0(X29,k3_xboole_0(X30,X31))|~r1_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_xboole_1])])])).
% 0.20/0.42  cnf(c_0_56, negated_conjecture, (r1_xboole_0(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.42  cnf(c_0_57, negated_conjecture, (k4_xboole_0(k4_xboole_0(esk5_0,esk5_0),X1)=k4_xboole_0(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_54])).
% 0.20/0.42  cnf(c_0_58, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(esk5_0,esk5_0))=X1), inference(spm,[status(thm)],[c_0_35, c_0_51])).
% 0.20/0.42  cnf(c_0_59, plain, (r1_xboole_0(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.42  fof(c_0_60, plain, ![X32, X33]:r1_xboole_0(k4_xboole_0(X32,X33),X33), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.20/0.42  fof(c_0_61, plain, ![X26, X27, X28]:((r1_xboole_0(X26,k2_xboole_0(X27,X28))|~r1_xboole_0(X26,X27)|~r1_xboole_0(X26,X28))&((r1_xboole_0(X26,X27)|~r1_xboole_0(X26,k2_xboole_0(X27,X28)))&(r1_xboole_0(X26,X28)|~r1_xboole_0(X26,k2_xboole_0(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.42  cnf(c_0_62, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_39, c_0_50])).
% 0.20/0.42  cnf(c_0_63, negated_conjecture, (r1_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_31, c_0_56])).
% 0.20/0.42  cnf(c_0_64, negated_conjecture, (k4_xboole_0(esk5_0,esk5_0)=k4_xboole_0(X1,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_57]), c_0_58])).
% 0.20/0.42  cnf(c_0_65, plain, (r1_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_59, c_0_34])).
% 0.20/0.42  cnf(c_0_66, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.42  cnf(c_0_67, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.42  cnf(c_0_68, plain, (r1_xboole_0(X1,k2_xboole_0(X2,X3))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.42  cnf(c_0_69, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(spm,[status(thm)],[c_0_62, c_0_50])).
% 0.20/0.42  cnf(c_0_70, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))=esk4_0), inference(spm,[status(thm)],[c_0_35, c_0_63])).
% 0.20/0.42  cnf(c_0_71, negated_conjecture, (k4_xboole_0(X1,k4_xboole_0(X2,X2))=X1), inference(spm,[status(thm)],[c_0_58, c_0_64])).
% 0.20/0.42  cnf(c_0_72, plain, (r1_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.42  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(rw,[status(thm)],[c_0_67, c_0_34])).
% 0.20/0.42  cnf(c_0_74, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(X1,esk5_0))|~r1_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_68, c_0_37])).
% 0.20/0.42  cnf(c_0_75, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_31, c_0_66])).
% 0.20/0.42  cnf(c_0_76, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_64]), c_0_71]), c_0_72])])).
% 0.20/0.42  cnf(c_0_77, plain, (r2_hidden(esk2_2(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1)))|r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_73, c_0_50])).
% 0.20/0.42  cnf(c_0_78, negated_conjecture, (r1_xboole_0(esk4_0,k2_xboole_0(k4_xboole_0(X1,esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.42  cnf(c_0_79, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.42  cnf(c_0_80, negated_conjecture, (r1_xboole_0(k2_xboole_0(k4_xboole_0(X1,esk4_0),esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_78])).
% 0.20/0.42  cnf(c_0_81, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=esk3_0), inference(spm,[status(thm)],[c_0_35, c_0_79])).
% 0.20/0.42  cnf(c_0_82, negated_conjecture, (~r1_xboole_0(k2_xboole_0(esk3_0,esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.42  cnf(c_0_83, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 84
% 0.20/0.42  # Proof object clause steps            : 55
% 0.20/0.42  # Proof object formula steps           : 29
% 0.20/0.42  # Proof object conjectures             : 33
% 0.20/0.42  # Proof object clause conjectures      : 30
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 19
% 0.20/0.42  # Proof object initial formulas used   : 14
% 0.20/0.42  # Proof object generating inferences   : 29
% 0.20/0.42  # Proof object simplifying inferences  : 19
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 14
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 24
% 0.20/0.42  # Removed in clause preprocessing      : 3
% 0.20/0.42  # Initial clauses in saturation        : 21
% 0.20/0.42  # Processed clauses                    : 752
% 0.20/0.42  # ...of these trivial                  : 58
% 0.20/0.42  # ...subsumed                          : 429
% 0.20/0.42  # ...remaining for further processing  : 265
% 0.20/0.42  # Other redundant clauses eliminated   : 8
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 11
% 0.20/0.42  # Backward-rewritten                   : 29
% 0.20/0.42  # Generated clauses                    : 4364
% 0.20/0.42  # ...of the previous two non-trivial   : 2132
% 0.20/0.42  # Contextual simplify-reflections      : 0
% 0.20/0.42  # Paramodulations                      : 4356
% 0.20/0.42  # Factorizations                       : 0
% 0.20/0.42  # Equation resolutions                 : 8
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
% 0.20/0.42  # Current number of processed clauses  : 204
% 0.20/0.42  #    Positive orientable unit clauses  : 132
% 0.20/0.42  #    Positive unorientable unit clauses: 2
% 0.20/0.42  #    Negative unit clauses             : 5
% 0.20/0.42  #    Non-unit-clauses                  : 65
% 0.20/0.42  # Current number of unprocessed clauses: 1359
% 0.20/0.42  # ...number of literals in the above   : 2066
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 64
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 820
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 718
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 216
% 0.20/0.42  # Unit Clause-clause subsumption calls : 96
% 0.20/0.42  # Rewrite failures with RHS unbound    : 89
% 0.20/0.42  # BW rewrite match attempts            : 363
% 0.20/0.42  # BW rewrite match successes           : 39
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 65396
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.071 s
% 0.20/0.42  # System time              : 0.006 s
% 0.20/0.42  # Total time               : 0.077 s
% 0.20/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
