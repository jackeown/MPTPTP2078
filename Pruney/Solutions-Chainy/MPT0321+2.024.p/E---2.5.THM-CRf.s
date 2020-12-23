%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:01 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 (1705 expanded)
%              Number of clauses        :   75 ( 765 expanded)
%              Number of leaves         :   14 ( 439 expanded)
%              Depth                    :   17
%              Number of atoms          :  177 (3533 expanded)
%              Number of equality atoms :  135 (2807 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t125_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
      & k2_zfmisc_1(X3,k4_xboole_0(X1,X2)) = k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t127_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_xboole_0(X1,X2)
        | r1_xboole_0(X3,X4) )
     => r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(t32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X2,X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X32,X33,X34,X35] : k2_zfmisc_1(k3_xboole_0(X32,X33),k3_xboole_0(X34,X35)) = k3_xboole_0(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X35)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k3_xboole_0(X24,X25) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_17,plain,(
    ! [X17,X18] :
      ( ( k4_xboole_0(X17,X18) != k1_xboole_0
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | k4_xboole_0(X17,X18) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

fof(c_0_18,plain,(
    ! [X21,X22] : r1_tarski(k4_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_19,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_20,plain,(
    ! [X36,X37,X38] :
      ( k2_zfmisc_1(k4_xboole_0(X36,X37),X38) = k4_xboole_0(k2_zfmisc_1(X36,X38),k2_zfmisc_1(X37,X38))
      & k2_zfmisc_1(X38,k4_xboole_0(X36,X37)) = k4_xboole_0(k2_zfmisc_1(X38,X36),k2_zfmisc_1(X38,X37)) ) ),
    inference(variable_rename,[status(thm)],[t125_zfmisc_1])).

fof(c_0_21,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0)
    & esk3_0 != k1_xboole_0
    & esk4_0 != k1_xboole_0
    & ( esk3_0 != esk5_0
      | esk4_0 != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_22,plain,(
    ! [X9,X10,X12,X13,X14] :
      ( ( r1_xboole_0(X9,X10)
        | r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X14,k3_xboole_0(X12,X13))
        | ~ r1_xboole_0(X12,X13) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_23,plain,(
    ! [X26,X27] : r1_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_24,plain,(
    ! [X23] : k4_xboole_0(X23,k1_xboole_0) = X23 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_25,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k2_zfmisc_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_36,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_26]),c_0_26])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,X2),X3) = k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk5_0,X1),k2_zfmisc_1(esk3_0,esk4_0)) = k2_zfmisc_1(esk5_0,k4_xboole_0(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_26])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_42,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk2_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_43,plain,(
    ! [X30,X31] :
      ( ( k2_zfmisc_1(X30,X31) != k1_xboole_0
        | X30 = k1_xboole_0
        | X31 = k1_xboole_0 )
      & ( X30 != k1_xboole_0
        | k2_zfmisc_1(X30,X31) = k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k2_zfmisc_1(X30,X31) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_44,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k4_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(X4,X2))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X4)),k4_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_34])).

cnf(c_0_45,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X4),k4_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_37]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),esk4_0) = k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_34]),c_0_41])])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k4_xboole_0(X2,X4)))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,X4)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),X1),k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0))) = k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_46])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r1_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_34])).

fof(c_0_55,plain,(
    ! [X39,X40,X41,X42] :
      ( ( ~ r1_xboole_0(X39,X40)
        | r1_xboole_0(k2_zfmisc_1(X39,X41),k2_zfmisc_1(X40,X42)) )
      & ( ~ r1_xboole_0(X41,X42)
        | r1_xboole_0(k2_zfmisc_1(X39,X41),k2_zfmisc_1(X40,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).

fof(c_0_56,plain,(
    ! [X19,X20] :
      ( k4_xboole_0(X19,X20) != k4_xboole_0(X20,X19)
      | X19 = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).

cnf(c_0_57,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),X1)) = k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk4_0,esk6_0)) = k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_46]),c_0_52]),c_0_53]),c_0_34]),c_0_36]),c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,esk6_0)) = k2_zfmisc_1(k4_xboole_0(esk5_0,X1),esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1)) = k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_61,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_48])).

cnf(c_0_62,plain,
    ( r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( X1 = X2
    | k4_xboole_0(X1,X2) != k4_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_65,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_30]),c_0_52]),c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),esk6_0) = k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),esk4_0) = k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1)) = k1_xboole_0
    | ~ r1_xboole_0(k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1)),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_70,plain,
    ( r1_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_33])).

cnf(c_0_71,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,X1) = k2_zfmisc_1(esk3_0,esk4_0)
    | k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1)) != k2_zfmisc_1(esk5_0,k4_xboole_0(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_39])).

cnf(c_0_72,plain,
    ( k4_xboole_0(X1,X2) = X1
    | k4_xboole_0(X1,k4_xboole_0(X1,X2)) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_36])).

cnf(c_0_73,negated_conjecture,
    ( k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)) = k1_xboole_0
    | k4_xboole_0(esk5_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X2)
    | k2_zfmisc_1(k4_xboole_0(X1,X3),X2) != k2_zfmisc_1(k4_xboole_0(X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_38]),c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk6_0,esk4_0)) = k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_66]),c_0_38])).

cnf(c_0_76,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk4_0)) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_67]),c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_79,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,X1) = k2_zfmisc_1(esk3_0,esk4_0)
    | k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1)) != k2_zfmisc_1(esk5_0,k4_xboole_0(X1,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_60])).

cnf(c_0_80,negated_conjecture,
    ( k4_xboole_0(esk5_0,esk3_0) = k1_xboole_0
    | k4_xboole_0(esk4_0,esk6_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk4_0)) = k2_zfmisc_1(esk3_0,k4_xboole_0(esk6_0,esk4_0))
    | k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk6_0,esk4_0)) != k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk5_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1)) = k2_zfmisc_1(esk3_0,esk4_0)
    | k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_36]),c_0_53])).

cnf(c_0_85,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = esk4_0
    | esk5_0 = esk3_0
    | k4_xboole_0(esk3_0,esk5_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k4_xboole_0(esk6_0,esk4_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_77]),c_0_82]),c_0_83]),c_0_82]),c_0_83])])).

cnf(c_0_87,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_88,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(esk5_0,esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_46])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1)) = k2_zfmisc_1(esk3_0,esk4_0)
    | k2_zfmisc_1(esk5_0,k4_xboole_0(X1,k4_xboole_0(X1,esk6_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_84,c_0_37])).

cnf(c_0_90,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = esk4_0
    | esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_82])])).

cnf(c_0_91,negated_conjecture,
    ( k4_xboole_0(esk6_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_86]),c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)),esk4_0) = k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_88]),c_0_37])).

cnf(c_0_93,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = k1_xboole_0
    | esk5_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91]),c_0_53]),c_0_52]),c_0_53])])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)) = k1_xboole_0
    | k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_92]),c_0_68])).

cnf(c_0_95,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_93]),c_0_68]),c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0)) = k1_xboole_0
    | k4_xboole_0(esk4_0,esk6_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_80]),c_0_83])).

cnf(c_0_97,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_82]),c_0_34]),c_0_87]),c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = esk4_0
    | k4_xboole_0(esk4_0,esk6_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_96]),c_0_87])).

cnf(c_0_99,negated_conjecture,
    ( esk3_0 != esk5_0
    | esk4_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_100,negated_conjecture,
    ( esk6_0 = esk4_0
    | k4_xboole_0(esk4_0,esk6_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_91])).

cnf(c_0_101,negated_conjecture,
    ( k4_xboole_0(esk4_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_52]),c_0_53])])).

cnf(c_0_102,negated_conjecture,
    ( esk6_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_95])])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_101])]),c_0_102]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:57:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.21/0.51  # and selection function SelectCQIPrecW.
% 0.21/0.51  #
% 0.21/0.51  # Preprocessing time       : 0.027 s
% 0.21/0.51  # Presaturation interreduction done
% 0.21/0.51  
% 0.21/0.51  # Proof found!
% 0.21/0.51  # SZS status Theorem
% 0.21/0.51  # SZS output start CNFRefutation
% 0.21/0.51  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.21/0.51  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.21/0.51  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.51  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.21/0.51  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.51  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.21/0.51  fof(t125_zfmisc_1, axiom, ![X1, X2, X3]:(k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&k2_zfmisc_1(X3,k4_xboole_0(X1,X2))=k4_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 0.21/0.51  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.21/0.51  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.21/0.51  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.21/0.51  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.51  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.51  fof(t127_zfmisc_1, axiom, ![X1, X2, X3, X4]:((r1_xboole_0(X1,X2)|r1_xboole_0(X3,X4))=>r1_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 0.21/0.51  fof(t32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k4_xboole_0(X2,X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 0.21/0.51  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.21/0.51  fof(c_0_15, plain, ![X32, X33, X34, X35]:k2_zfmisc_1(k3_xboole_0(X32,X33),k3_xboole_0(X34,X35))=k3_xboole_0(k2_zfmisc_1(X32,X34),k2_zfmisc_1(X33,X35)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.21/0.51  fof(c_0_16, plain, ![X24, X25]:k4_xboole_0(X24,k4_xboole_0(X24,X25))=k3_xboole_0(X24,X25), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.51  fof(c_0_17, plain, ![X17, X18]:((k4_xboole_0(X17,X18)!=k1_xboole_0|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|k4_xboole_0(X17,X18)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.21/0.51  fof(c_0_18, plain, ![X21, X22]:r1_tarski(k4_xboole_0(X21,X22),X21), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.51  fof(c_0_19, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.21/0.51  fof(c_0_20, plain, ![X36, X37, X38]:(k2_zfmisc_1(k4_xboole_0(X36,X37),X38)=k4_xboole_0(k2_zfmisc_1(X36,X38),k2_zfmisc_1(X37,X38))&k2_zfmisc_1(X38,k4_xboole_0(X36,X37))=k4_xboole_0(k2_zfmisc_1(X38,X36),k2_zfmisc_1(X38,X37))), inference(variable_rename,[status(thm)],[t125_zfmisc_1])).
% 0.21/0.51  fof(c_0_21, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)&((esk3_0!=k1_xboole_0&esk4_0!=k1_xboole_0)&(esk3_0!=esk5_0|esk4_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.21/0.51  fof(c_0_22, plain, ![X9, X10, X12, X13, X14]:((r1_xboole_0(X9,X10)|r2_hidden(esk1_2(X9,X10),k3_xboole_0(X9,X10)))&(~r2_hidden(X14,k3_xboole_0(X12,X13))|~r1_xboole_0(X12,X13))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.21/0.51  fof(c_0_23, plain, ![X26, X27]:r1_xboole_0(k4_xboole_0(X26,X27),X27), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.21/0.51  fof(c_0_24, plain, ![X23]:k4_xboole_0(X23,k1_xboole_0)=X23, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.21/0.51  cnf(c_0_25, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.51  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.51  cnf(c_0_27, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.51  cnf(c_0_28, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.51  cnf(c_0_29, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  cnf(c_0_30, plain, (k2_zfmisc_1(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_31, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k2_zfmisc_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.51  cnf(c_0_32, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.51  cnf(c_0_33, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.51  cnf(c_0_34, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.51  cnf(c_0_35, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_26]), c_0_26])).
% 0.21/0.51  cnf(c_0_36, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.51  cnf(c_0_37, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_26]), c_0_26])).
% 0.21/0.51  cnf(c_0_38, plain, (k2_zfmisc_1(k4_xboole_0(X1,X2),X3)=k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_39, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk5_0,X1),k2_zfmisc_1(esk3_0,esk4_0))=k2_zfmisc_1(esk5_0,k4_xboole_0(X1,esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.51  cnf(c_0_40, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_32, c_0_26])).
% 0.21/0.51  cnf(c_0_41, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.51  fof(c_0_42, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk2_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.51  fof(c_0_43, plain, ![X30, X31]:((k2_zfmisc_1(X30,X31)!=k1_xboole_0|(X30=k1_xboole_0|X31=k1_xboole_0))&((X30!=k1_xboole_0|k2_zfmisc_1(X30,X31)=k1_xboole_0)&(X31!=k1_xboole_0|k2_zfmisc_1(X30,X31)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.51  cnf(c_0_44, plain, (k4_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k4_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(X4,X2)))=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X4)),k4_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_34])).
% 0.21/0.51  cnf(c_0_45, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X4),k4_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_37]), c_0_35])).
% 0.21/0.51  cnf(c_0_46, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),esk4_0)=k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.51  cnf(c_0_47, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_34]), c_0_41])])).
% 0.21/0.51  cnf(c_0_48, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.51  cnf(c_0_49, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.51  cnf(c_0_50, plain, (k4_xboole_0(k2_zfmisc_1(X1,X2),k4_xboole_0(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,k4_xboole_0(X2,X4))))=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X3)),k4_xboole_0(X2,X4))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.51  cnf(c_0_51, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),X1),k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0)))=k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(X1,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_46])).
% 0.21/0.51  cnf(c_0_52, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.51  cnf(c_0_53, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 0.21/0.51  cnf(c_0_54, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r1_xboole_0(k4_xboole_0(X2,X3),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_34])).
% 0.21/0.51  fof(c_0_55, plain, ![X39, X40, X41, X42]:((~r1_xboole_0(X39,X40)|r1_xboole_0(k2_zfmisc_1(X39,X41),k2_zfmisc_1(X40,X42)))&(~r1_xboole_0(X41,X42)|r1_xboole_0(k2_zfmisc_1(X39,X41),k2_zfmisc_1(X40,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_zfmisc_1])])])).
% 0.21/0.51  fof(c_0_56, plain, ![X19, X20]:(k4_xboole_0(X19,X20)!=k4_xboole_0(X20,X19)|X19=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_xboole_1])])).
% 0.21/0.51  cnf(c_0_57, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0)),k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),X1))=k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_46])).
% 0.21/0.51  cnf(c_0_58, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk4_0,esk6_0))=k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_46]), c_0_52]), c_0_53]), c_0_34]), c_0_36]), c_0_34])).
% 0.21/0.51  cnf(c_0_59, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(X1,esk6_0))=k2_zfmisc_1(k4_xboole_0(esk5_0,X1),esk6_0)), inference(spm,[status(thm)],[c_0_38, c_0_31])).
% 0.21/0.51  cnf(c_0_60, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1))=k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.51  cnf(c_0_61, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_54, c_0_48])).
% 0.21/0.51  cnf(c_0_62, plain, (r1_xboole_0(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X4,X2))|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.51  cnf(c_0_63, plain, (X1=X2|k4_xboole_0(X1,X2)!=k4_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.21/0.51  cnf(c_0_64, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.51  cnf(c_0_65, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_30]), c_0_52]), c_0_53])).
% 0.21/0.51  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),esk6_0)=k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_59])).
% 0.21/0.51  cnf(c_0_67, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),esk4_0)=k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_38, c_0_60])).
% 0.21/0.51  cnf(c_0_68, negated_conjecture, (esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.51  cnf(c_0_69, negated_conjecture, (k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1))=k1_xboole_0|~r1_xboole_0(k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1)),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.21/0.51  cnf(c_0_70, plain, (r1_xboole_0(k2_zfmisc_1(X1,k4_xboole_0(X2,X3)),k2_zfmisc_1(X4,X3))), inference(spm,[status(thm)],[c_0_62, c_0_33])).
% 0.21/0.51  cnf(c_0_71, negated_conjecture, (k2_zfmisc_1(esk5_0,X1)=k2_zfmisc_1(esk3_0,esk4_0)|k4_xboole_0(k2_zfmisc_1(esk3_0,esk4_0),k2_zfmisc_1(esk5_0,X1))!=k2_zfmisc_1(esk5_0,k4_xboole_0(X1,esk6_0))), inference(spm,[status(thm)],[c_0_63, c_0_39])).
% 0.21/0.51  cnf(c_0_72, plain, (k4_xboole_0(X1,X2)=X1|k4_xboole_0(X1,k4_xboole_0(X1,X2))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_36])).
% 0.21/0.51  cnf(c_0_73, negated_conjecture, (k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0))=k1_xboole_0|k4_xboole_0(esk5_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.51  cnf(c_0_74, plain, (k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X2)|k2_zfmisc_1(k4_xboole_0(X1,X3),X2)!=k2_zfmisc_1(k4_xboole_0(X3,X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_38]), c_0_38])).
% 0.21/0.51  cnf(c_0_75, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk5_0,esk3_0),k4_xboole_0(esk6_0,esk4_0))=k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk4_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_66]), c_0_38])).
% 0.21/0.51  cnf(c_0_76, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)=k1_xboole_0|k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk4_0))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_67]), c_0_68])).
% 0.21/0.51  cnf(c_0_77, negated_conjecture, (k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.21/0.51  cnf(c_0_78, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.51  cnf(c_0_79, negated_conjecture, (k2_zfmisc_1(esk5_0,X1)=k2_zfmisc_1(esk3_0,esk4_0)|k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1))!=k2_zfmisc_1(esk5_0,k4_xboole_0(X1,esk6_0))), inference(rw,[status(thm)],[c_0_71, c_0_60])).
% 0.21/0.51  cnf(c_0_80, negated_conjecture, (k4_xboole_0(esk5_0,esk3_0)=k1_xboole_0|k4_xboole_0(esk4_0,esk6_0)=esk4_0), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.21/0.51  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,esk4_0))=k2_zfmisc_1(esk3_0,k4_xboole_0(esk6_0,esk4_0))|k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk6_0,esk4_0))!=k2_zfmisc_1(k4_xboole_0(esk3_0,esk5_0),k4_xboole_0(esk4_0,esk6_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.21/0.51  cnf(c_0_82, negated_conjecture, (k4_xboole_0(esk3_0,esk5_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.21/0.51  cnf(c_0_83, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_78])).
% 0.21/0.51  cnf(c_0_84, negated_conjecture, (k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1))=k2_zfmisc_1(esk3_0,esk4_0)|k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(esk6_0,X1)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_36]), c_0_53])).
% 0.21/0.51  cnf(c_0_85, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=esk4_0|esk5_0=esk3_0|k4_xboole_0(esk3_0,esk5_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_80])).
% 0.21/0.51  cnf(c_0_86, negated_conjecture, (k2_zfmisc_1(esk3_0,k4_xboole_0(esk6_0,esk4_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_77]), c_0_82]), c_0_83]), c_0_82]), c_0_83])])).
% 0.21/0.51  cnf(c_0_87, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.51  cnf(c_0_88, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(X1,esk4_0),k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,esk6_0)))=k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(esk5_0,esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_46])).
% 0.21/0.51  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk5_0,k4_xboole_0(esk6_0,X1))=k2_zfmisc_1(esk3_0,esk4_0)|k2_zfmisc_1(esk5_0,k4_xboole_0(X1,k4_xboole_0(X1,esk6_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_84, c_0_37])).
% 0.21/0.51  cnf(c_0_90, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=esk4_0|esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_82])])).
% 0.21/0.51  cnf(c_0_91, negated_conjecture, (k4_xboole_0(esk6_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_86]), c_0_87])).
% 0.21/0.51  cnf(c_0_92, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0)),esk4_0)=k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_88]), c_0_37])).
% 0.21/0.51  cnf(c_0_93, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=k1_xboole_0|esk5_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_91]), c_0_53]), c_0_52]), c_0_53])])).
% 0.21/0.51  cnf(c_0_94, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk5_0))=k1_xboole_0|k2_zfmisc_1(esk5_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))!=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_92]), c_0_68])).
% 0.21/0.51  cnf(c_0_95, negated_conjecture, (esk5_0=esk3_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_93]), c_0_68]), c_0_87])).
% 0.21/0.51  cnf(c_0_96, negated_conjecture, (k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,esk6_0))=k1_xboole_0|k4_xboole_0(esk4_0,esk6_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_80]), c_0_83])).
% 0.21/0.51  cnf(c_0_97, negated_conjecture, (k2_zfmisc_1(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk6_0)))!=k1_xboole_0), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_82]), c_0_34]), c_0_87]), c_0_95])).
% 0.21/0.51  cnf(c_0_98, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=esk4_0|k4_xboole_0(esk4_0,esk6_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_96]), c_0_87])).
% 0.21/0.51  cnf(c_0_99, negated_conjecture, (esk3_0!=esk5_0|esk4_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.51  cnf(c_0_100, negated_conjecture, (esk6_0=esk4_0|k4_xboole_0(esk4_0,esk6_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_91])).
% 0.21/0.51  cnf(c_0_101, negated_conjecture, (k4_xboole_0(esk4_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_52]), c_0_53])])).
% 0.21/0.51  cnf(c_0_102, negated_conjecture, (esk6_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_95])])).
% 0.21/0.51  cnf(c_0_103, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_101])]), c_0_102]), ['proof']).
% 0.21/0.51  # SZS output end CNFRefutation
% 0.21/0.51  # Proof object total steps             : 104
% 0.21/0.51  # Proof object clause steps            : 75
% 0.21/0.51  # Proof object formula steps           : 29
% 0.21/0.51  # Proof object conjectures             : 45
% 0.21/0.51  # Proof object clause conjectures      : 42
% 0.21/0.51  # Proof object formula conjectures     : 3
% 0.21/0.51  # Proof object initial clauses used    : 20
% 0.21/0.51  # Proof object initial formulas used   : 14
% 0.21/0.51  # Proof object generating inferences   : 42
% 0.21/0.51  # Proof object simplifying inferences  : 62
% 0.21/0.51  # Training examples: 0 positive, 0 negative
% 0.21/0.51  # Parsed axioms                        : 16
% 0.21/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.51  # Initial clauses                      : 26
% 0.21/0.51  # Removed in clause preprocessing      : 1
% 0.21/0.51  # Initial clauses in saturation        : 25
% 0.21/0.51  # Processed clauses                    : 1085
% 0.21/0.51  # ...of these trivial                  : 32
% 0.21/0.51  # ...subsumed                          : 705
% 0.21/0.51  # ...remaining for further processing  : 348
% 0.21/0.51  # Other redundant clauses eliminated   : 20
% 0.21/0.51  # Clauses deleted for lack of memory   : 0
% 0.21/0.51  # Backward-subsumed                    : 19
% 0.21/0.51  # Backward-rewritten                   : 173
% 0.21/0.51  # Generated clauses                    : 10538
% 0.21/0.51  # ...of the previous two non-trivial   : 8282
% 0.21/0.51  # Contextual simplify-reflections      : 0
% 0.21/0.51  # Paramodulations                      : 10511
% 0.21/0.51  # Factorizations                       : 2
% 0.21/0.51  # Equation resolutions                 : 25
% 0.21/0.51  # Propositional unsat checks           : 0
% 0.21/0.51  #    Propositional check models        : 0
% 0.21/0.51  #    Propositional check unsatisfiable : 0
% 0.21/0.51  #    Propositional clauses             : 0
% 0.21/0.51  #    Propositional clauses after purity: 0
% 0.21/0.51  #    Propositional unsat core size     : 0
% 0.21/0.51  #    Propositional preprocessing time  : 0.000
% 0.21/0.51  #    Propositional encoding time       : 0.000
% 0.21/0.51  #    Propositional solver time         : 0.000
% 0.21/0.51  #    Success case prop preproc time    : 0.000
% 0.21/0.51  #    Success case prop encoding time   : 0.000
% 0.21/0.51  #    Success case prop solver time     : 0.000
% 0.21/0.51  # Current number of processed clauses  : 129
% 0.21/0.51  #    Positive orientable unit clauses  : 48
% 0.21/0.51  #    Positive unorientable unit clauses: 3
% 0.21/0.51  #    Negative unit clauses             : 8
% 0.21/0.51  #    Non-unit-clauses                  : 70
% 0.21/0.51  # Current number of unprocessed clauses: 7185
% 0.21/0.51  # ...number of literals in the above   : 11306
% 0.21/0.51  # Current number of archived formulas  : 0
% 0.21/0.51  # Current number of archived clauses   : 218
% 0.21/0.51  # Clause-clause subsumption calls (NU) : 2867
% 0.21/0.51  # Rec. Clause-clause subsumption calls : 2606
% 0.21/0.51  # Non-unit clause-clause subsumptions  : 329
% 0.21/0.51  # Unit Clause-clause subsumption calls : 177
% 0.21/0.51  # Rewrite failures with RHS unbound    : 0
% 0.21/0.51  # BW rewrite match attempts            : 254
% 0.21/0.51  # BW rewrite match successes           : 91
% 0.21/0.51  # Condensation attempts                : 0
% 0.21/0.51  # Condensation successes               : 0
% 0.21/0.51  # Termbank termtop insertions          : 181393
% 0.21/0.51  
% 0.21/0.51  # -------------------------------------------------
% 0.21/0.51  # User time                : 0.154 s
% 0.21/0.51  # System time              : 0.011 s
% 0.21/0.51  # Total time               : 0.164 s
% 0.21/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
