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
% DateTime   : Thu Dec  3 10:37:50 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 830 expanded)
%              Number of clauses        :   63 ( 341 expanded)
%              Number of leaves         :   15 ( 239 expanded)
%              Depth                    :   21
%              Number of atoms          :  223 (1512 expanded)
%              Number of equality atoms :  107 (1082 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t18_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

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

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t1_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k5_xboole_0(X2,X3))
    <=> ~ ( r2_hidden(X1,X2)
        <=> r2_hidden(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(c_0_15,plain,(
    ! [X23,X24] : r1_xboole_0(k4_xboole_0(X23,X24),X24) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_16,plain,(
    ! [X19,X20] : k4_xboole_0(X19,X20) = k5_xboole_0(X19,k3_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_17,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r1_xboole_0(X11,X12)
        | r2_hidden(esk1_2(X11,X12),k3_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X16,k3_xboole_0(X14,X15))
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(X7,X6) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(X1)
       => X1 = X2 ) ),
    inference(assume_negation,[status(cth)],[t18_zfmisc_1])).

fof(c_0_22,plain,(
    ! [X22] : k4_xboole_0(X22,k1_xboole_0) = X22 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_27,plain,(
    ! [X43] : k2_tarski(X43,X43) = k1_tarski(X43) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_28,plain,(
    ! [X44,X45] : k1_enumset1(X44,X44,X45) = k2_tarski(X44,X45) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_29,plain,(
    ! [X46,X47,X48] : k2_enumset1(X46,X46,X47,X48) = k1_enumset1(X46,X47,X48) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_30,plain,(
    ! [X49,X50,X51,X52] : k3_enumset1(X49,X49,X50,X51,X52) = k2_enumset1(X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_31,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31,X32,X33,X34] :
      ( ( ~ r2_hidden(X29,X28)
        | X29 = X25
        | X29 = X26
        | X29 = X27
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X25
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X26
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( X30 != X27
        | r2_hidden(X30,X28)
        | X28 != k1_enumset1(X25,X26,X27) )
      & ( esk3_4(X31,X32,X33,X34) != X31
        | ~ r2_hidden(esk3_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk3_4(X31,X32,X33,X34) != X32
        | ~ r2_hidden(esk3_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( esk3_4(X31,X32,X33,X34) != X33
        | ~ r2_hidden(esk3_4(X31,X32,X33,X34),X34)
        | X34 = k1_enumset1(X31,X32,X33) )
      & ( r2_hidden(esk3_4(X31,X32,X33,X34),X34)
        | esk3_4(X31,X32,X33,X34) = X31
        | esk3_4(X31,X32,X33,X34) = X32
        | esk3_4(X31,X32,X33,X34) = X33
        | X34 = k1_enumset1(X31,X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_32,plain,(
    ! [X21] : k3_xboole_0(X21,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k3_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0)) = k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X4)
    | esk3_4(X1,X2,X3,X4) = X1
    | esk3_4(X1,X2,X3,X4) = X2
    | esk3_4(X1,X2,X3,X4) = X3
    | X4 = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(rw,[status(thm)],[c_0_33,c_0_19])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_25])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36]),c_0_36]),c_0_36]),c_0_37]),c_0_37]),c_0_37]),c_0_38]),c_0_38]),c_0_38]),c_0_39]),c_0_39]),c_0_39])).

cnf(c_0_46,plain,
    ( esk3_4(X1,X2,X3,X4) = X3
    | esk3_4(X1,X2,X3,X4) = X2
    | esk3_4(X1,X2,X3,X4) = X1
    | X4 = k3_enumset1(X1,X1,X1,X2,X3)
    | r2_hidden(esk3_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_38]),c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_38]),c_0_39])).

fof(c_0_48,plain,(
    ! [X17] :
      ( X17 = k1_xboole_0
      | r2_hidden(esk2_1(X17),X17) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_49,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_50,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(rw,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( ~ r2_hidden(X1,k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1) = k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)
    | esk3_4(esk6_0,esk6_0,esk6_0,X1) = esk6_0
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_49]),c_0_50]),c_0_42])).

cnf(c_0_56,plain,
    ( X4 = k1_enumset1(X1,X2,X3)
    | esk3_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk3_4(X1,X2,X3,X4),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_57,negated_conjecture,
    ( esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk6_0
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | ~ r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_1(k3_enumset1(X1,X1,X1,X2,X3)),k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

fof(c_0_59,plain,(
    ! [X8,X9,X10] :
      ( ( ~ r2_hidden(X8,X9)
        | ~ r2_hidden(X8,X10)
        | ~ r2_hidden(X8,k5_xboole_0(X9,X10)) )
      & ( r2_hidden(X8,X9)
        | r2_hidden(X8,X10)
        | ~ r2_hidden(X8,k5_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X8,X9)
        | r2_hidden(X8,X10)
        | r2_hidden(X8,k5_xboole_0(X9,X10)) )
      & ( ~ r2_hidden(X8,X10)
        | r2_hidden(X8,X9)
        | r2_hidden(X8,k5_xboole_0(X9,X10)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).

cnf(c_0_60,plain,
    ( X4 = k3_enumset1(X1,X1,X1,X2,X3)
    | esk3_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk3_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_38]),c_0_39])).

cnf(c_0_61,negated_conjecture,
    ( esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk6_0
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,k5_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | ~ r2_hidden(esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_62,c_0_53])).

cnf(c_0_65,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_66,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_65]),c_0_45])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_69,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_38]),c_0_39])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k5_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_58])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_38]),c_0_39])).

cnf(c_0_73,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk6_0
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),X4))
    | r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_62,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) = k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_76]),c_0_77])).

fof(c_0_79,plain,(
    ! [X53,X54] :
      ( ~ r1_xboole_0(k1_tarski(X53),X54)
      | ~ r2_hidden(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_80,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk2_1(k3_xboole_0(X2,X1)),k3_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_54])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | ~ r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_78]),c_0_45])).

cnf(c_0_82,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | esk3_4(esk6_0,esk6_0,esk6_0,X1) = esk6_0
    | r2_hidden(esk2_1(k3_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_58])).

cnf(c_0_85,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_86,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_87,negated_conjecture,
    ( esk3_4(esk6_0,esk6_0,esk6_0,X1) = esk6_0
    | r2_hidden(esk2_1(k3_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_83]),c_0_55])).

cnf(c_0_88,negated_conjecture,
    ( esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))) = esk5_0
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_90,plain,
    ( r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( r2_hidden(esk5_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))
    | r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_25]),c_0_25]),c_0_89]),c_0_51])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_51])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_92]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.66  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.46/0.66  # and selection function SelectNegativeLiterals.
% 0.46/0.66  #
% 0.46/0.66  # Preprocessing time       : 0.028 s
% 0.46/0.66  # Presaturation interreduction done
% 0.46/0.66  
% 0.46/0.66  # Proof found!
% 0.46/0.66  # SZS status Theorem
% 0.46/0.66  # SZS output start CNFRefutation
% 0.46/0.66  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.46/0.66  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.46/0.66  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.46/0.66  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.46/0.66  fof(t18_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 0.46/0.66  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.46/0.66  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.46/0.66  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.46/0.66  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.46/0.66  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.46/0.66  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.46/0.66  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.46/0.66  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.46/0.66  fof(t1_xboole_0, axiom, ![X1, X2, X3]:(r2_hidden(X1,k5_xboole_0(X2,X3))<=>~((r2_hidden(X1,X2)<=>r2_hidden(X1,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 0.46/0.66  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.46/0.66  fof(c_0_15, plain, ![X23, X24]:r1_xboole_0(k4_xboole_0(X23,X24),X24), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.46/0.66  fof(c_0_16, plain, ![X19, X20]:k4_xboole_0(X19,X20)=k5_xboole_0(X19,k3_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.46/0.66  fof(c_0_17, plain, ![X11, X12, X14, X15, X16]:((r1_xboole_0(X11,X12)|r2_hidden(esk1_2(X11,X12),k3_xboole_0(X11,X12)))&(~r2_hidden(X16,k3_xboole_0(X14,X15))|~r1_xboole_0(X14,X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.46/0.66  cnf(c_0_18, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.46/0.66  cnf(c_0_19, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.46/0.66  fof(c_0_20, plain, ![X6, X7]:k3_xboole_0(X6,X7)=k3_xboole_0(X7,X6), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.46/0.66  fof(c_0_21, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_tarski(X1)=>X1=X2)), inference(assume_negation,[status(cth)],[t18_zfmisc_1])).
% 0.46/0.66  fof(c_0_22, plain, ![X22]:k4_xboole_0(X22,k1_xboole_0)=X22, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.46/0.66  cnf(c_0_23, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.66  cnf(c_0_24, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.46/0.66  cnf(c_0_25, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.46/0.66  fof(c_0_26, negated_conjecture, (k3_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)&esk5_0!=esk6_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.46/0.66  fof(c_0_27, plain, ![X43]:k2_tarski(X43,X43)=k1_tarski(X43), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.46/0.66  fof(c_0_28, plain, ![X44, X45]:k1_enumset1(X44,X44,X45)=k2_tarski(X44,X45), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.46/0.66  fof(c_0_29, plain, ![X46, X47, X48]:k2_enumset1(X46,X46,X47,X48)=k1_enumset1(X46,X47,X48), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.46/0.66  fof(c_0_30, plain, ![X49, X50, X51, X52]:k3_enumset1(X49,X49,X50,X51,X52)=k2_enumset1(X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.46/0.66  fof(c_0_31, plain, ![X25, X26, X27, X28, X29, X30, X31, X32, X33, X34]:(((~r2_hidden(X29,X28)|(X29=X25|X29=X26|X29=X27)|X28!=k1_enumset1(X25,X26,X27))&(((X30!=X25|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))&(X30!=X26|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27)))&(X30!=X27|r2_hidden(X30,X28)|X28!=k1_enumset1(X25,X26,X27))))&((((esk3_4(X31,X32,X33,X34)!=X31|~r2_hidden(esk3_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33))&(esk3_4(X31,X32,X33,X34)!=X32|~r2_hidden(esk3_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(esk3_4(X31,X32,X33,X34)!=X33|~r2_hidden(esk3_4(X31,X32,X33,X34),X34)|X34=k1_enumset1(X31,X32,X33)))&(r2_hidden(esk3_4(X31,X32,X33,X34),X34)|(esk3_4(X31,X32,X33,X34)=X31|esk3_4(X31,X32,X33,X34)=X32|esk3_4(X31,X32,X33,X34)=X33)|X34=k1_enumset1(X31,X32,X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.46/0.66  fof(c_0_32, plain, ![X21]:k3_xboole_0(X21,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.46/0.66  cnf(c_0_33, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.46/0.66  cnf(c_0_34, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.46/0.66  cnf(c_0_35, negated_conjecture, (k3_xboole_0(k1_tarski(esk5_0),k1_tarski(esk6_0))=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.46/0.66  cnf(c_0_36, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.46/0.66  cnf(c_0_37, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.66  cnf(c_0_38, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.46/0.66  cnf(c_0_39, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.46/0.66  cnf(c_0_40, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X4)|esk3_4(X1,X2,X3,X4)=X1|esk3_4(X1,X2,X3,X4)=X2|esk3_4(X1,X2,X3,X4)=X3|X4=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.66  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.66  cnf(c_0_42, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.46/0.66  cnf(c_0_43, plain, (k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))=X1), inference(rw,[status(thm)],[c_0_33, c_0_19])).
% 0.46/0.66  cnf(c_0_44, plain, (~r2_hidden(X1,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))))), inference(spm,[status(thm)],[c_0_34, c_0_25])).
% 0.46/0.66  cnf(c_0_45, negated_conjecture, (k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36]), c_0_36]), c_0_36]), c_0_37]), c_0_37]), c_0_37]), c_0_38]), c_0_38]), c_0_38]), c_0_39]), c_0_39]), c_0_39])).
% 0.46/0.66  cnf(c_0_46, plain, (esk3_4(X1,X2,X3,X4)=X3|esk3_4(X1,X2,X3,X4)=X2|esk3_4(X1,X2,X3,X4)=X1|X4=k3_enumset1(X1,X1,X1,X2,X3)|r2_hidden(esk3_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_38]), c_0_39])).
% 0.46/0.66  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_38]), c_0_39])).
% 0.46/0.66  fof(c_0_48, plain, ![X17]:(X17=k1_xboole_0|r2_hidden(esk2_1(X17),X17)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.46/0.66  cnf(c_0_49, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.46/0.66  cnf(c_0_50, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(rw,[status(thm)],[c_0_43, c_0_42])).
% 0.46/0.66  cnf(c_0_51, negated_conjecture, (~r2_hidden(X1,k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.46/0.66  cnf(c_0_52, negated_conjecture, (k3_xboole_0(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0),X1)=k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)|esk3_4(esk6_0,esk6_0,esk6_0,X1)=esk6_0|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.46/0.66  cnf(c_0_53, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 0.46/0.66  cnf(c_0_54, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.46/0.66  cnf(c_0_55, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_49]), c_0_50]), c_0_42])).
% 0.46/0.66  cnf(c_0_56, plain, (X4=k1_enumset1(X1,X2,X3)|esk3_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk3_4(X1,X2,X3,X4),X4)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.66  cnf(c_0_57, negated_conjecture, (esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk6_0|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|~r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.46/0.66  cnf(c_0_58, plain, (r2_hidden(esk2_1(k3_enumset1(X1,X1,X1,X2,X3)),k3_enumset1(X1,X1,X1,X2,X3))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.46/0.66  fof(c_0_59, plain, ![X8, X9, X10]:(((~r2_hidden(X8,X9)|~r2_hidden(X8,X10)|~r2_hidden(X8,k5_xboole_0(X9,X10)))&(r2_hidden(X8,X9)|r2_hidden(X8,X10)|~r2_hidden(X8,k5_xboole_0(X9,X10))))&((~r2_hidden(X8,X9)|r2_hidden(X8,X10)|r2_hidden(X8,k5_xboole_0(X9,X10)))&(~r2_hidden(X8,X10)|r2_hidden(X8,X9)|r2_hidden(X8,k5_xboole_0(X9,X10))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_0])])])).
% 0.46/0.66  cnf(c_0_60, plain, (X4=k3_enumset1(X1,X1,X1,X2,X3)|esk3_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk3_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_38]), c_0_39])).
% 0.46/0.66  cnf(c_0_61, negated_conjecture, (esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk6_0|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.46/0.66  cnf(c_0_62, plain, (r2_hidden(X1,X3)|r2_hidden(X1,k5_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.46/0.66  cnf(c_0_63, negated_conjecture, (k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|~r2_hidden(esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.46/0.66  cnf(c_0_64, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X2,X2,X2,X3,X1),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_62, c_0_53])).
% 0.46/0.66  cnf(c_0_65, negated_conjecture, (k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.46/0.66  cnf(c_0_66, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.66  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_65]), c_0_45])).
% 0.46/0.66  cnf(c_0_68, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.46/0.66  cnf(c_0_69, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_38]), c_0_39])).
% 0.46/0.66  cnf(c_0_70, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k5_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.46/0.66  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_67, c_0_58])).
% 0.46/0.66  cnf(c_0_72, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X4,X5)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_38]), c_0_39])).
% 0.46/0.66  cnf(c_0_73, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_69])).
% 0.46/0.66  cnf(c_0_74, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.46/0.66  cnf(c_0_75, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_72])])).
% 0.46/0.66  cnf(c_0_76, negated_conjecture, (esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk6_0|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.46/0.66  cnf(c_0_77, plain, (r2_hidden(X1,k5_xboole_0(k3_enumset1(X1,X1,X1,X2,X3),X4))|r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_62, c_0_75])).
% 0.46/0.66  cnf(c_0_78, negated_conjecture, (k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))=k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_76]), c_0_77])).
% 0.46/0.66  fof(c_0_79, plain, ![X53, X54]:(~r1_xboole_0(k1_tarski(X53),X54)|~r2_hidden(X53,X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.46/0.66  cnf(c_0_80, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk2_1(k3_xboole_0(X2,X1)),k3_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_25, c_0_54])).
% 0.46/0.66  cnf(c_0_81, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|~r2_hidden(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_78]), c_0_45])).
% 0.46/0.66  cnf(c_0_82, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.46/0.66  cnf(c_0_83, negated_conjecture, (k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|esk3_4(esk6_0,esk6_0,esk6_0,X1)=esk6_0|r2_hidden(esk2_1(k3_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_52, c_0_80])).
% 0.46/0.66  cnf(c_0_84, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_81, c_0_58])).
% 0.46/0.66  cnf(c_0_85, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.46/0.66  cnf(c_0_86, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.66  cnf(c_0_87, negated_conjecture, (esk3_4(esk6_0,esk6_0,esk6_0,X1)=esk6_0|r2_hidden(esk2_1(k3_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))),k3_xboole_0(X1,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(esk3_4(esk6_0,esk6_0,esk6_0,X1),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_83]), c_0_55])).
% 0.46/0.66  cnf(c_0_88, negated_conjecture, (esk3_4(esk6_0,esk6_0,esk6_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))=esk5_0|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_73, c_0_84])).
% 0.46/0.66  cnf(c_0_89, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.46/0.66  cnf(c_0_90, plain, (r2_hidden(esk1_2(k3_enumset1(X1,X1,X1,X1,X1),X2),k3_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.46/0.66  cnf(c_0_91, negated_conjecture, (r2_hidden(esk5_0,k5_xboole_0(k3_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0)))|r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_25]), c_0_25]), c_0_89]), c_0_51])).
% 0.46/0.66  cnf(c_0_92, negated_conjecture, (r2_hidden(esk6_0,k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_51])).
% 0.46/0.66  cnf(c_0_93, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_92]), c_0_89]), ['proof']).
% 0.46/0.66  # SZS output end CNFRefutation
% 0.46/0.66  # Proof object total steps             : 94
% 0.46/0.66  # Proof object clause steps            : 63
% 0.46/0.66  # Proof object formula steps           : 31
% 0.46/0.66  # Proof object conjectures             : 25
% 0.46/0.66  # Proof object clause conjectures      : 22
% 0.46/0.66  # Proof object formula conjectures     : 3
% 0.46/0.66  # Proof object initial clauses used    : 22
% 0.46/0.66  # Proof object initial formulas used   : 15
% 0.46/0.66  # Proof object generating inferences   : 28
% 0.46/0.66  # Proof object simplifying inferences  : 48
% 0.46/0.66  # Training examples: 0 positive, 0 negative
% 0.46/0.66  # Parsed axioms                        : 16
% 0.46/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.66  # Initial clauses                      : 31
% 0.46/0.66  # Removed in clause preprocessing      : 5
% 0.46/0.66  # Initial clauses in saturation        : 26
% 0.46/0.66  # Processed clauses                    : 1780
% 0.46/0.66  # ...of these trivial                  : 49
% 0.46/0.66  # ...subsumed                          : 1299
% 0.46/0.66  # ...remaining for further processing  : 432
% 0.46/0.66  # Other redundant clauses eliminated   : 158
% 0.46/0.66  # Clauses deleted for lack of memory   : 0
% 0.46/0.66  # Backward-subsumed                    : 33
% 0.46/0.66  # Backward-rewritten                   : 29
% 0.46/0.66  # Generated clauses                    : 22033
% 0.46/0.66  # ...of the previous two non-trivial   : 19354
% 0.46/0.66  # Contextual simplify-reflections      : 1
% 0.46/0.66  # Paramodulations                      : 21858
% 0.46/0.66  # Factorizations                       : 21
% 0.46/0.66  # Equation resolutions                 : 158
% 0.46/0.66  # Propositional unsat checks           : 0
% 0.46/0.66  #    Propositional check models        : 0
% 0.46/0.66  #    Propositional check unsatisfiable : 0
% 0.46/0.66  #    Propositional clauses             : 0
% 0.46/0.66  #    Propositional clauses after purity: 0
% 0.46/0.66  #    Propositional unsat core size     : 0
% 0.46/0.66  #    Propositional preprocessing time  : 0.000
% 0.46/0.66  #    Propositional encoding time       : 0.000
% 0.46/0.66  #    Propositional solver time         : 0.000
% 0.46/0.66  #    Success case prop preproc time    : 0.000
% 0.46/0.66  #    Success case prop encoding time   : 0.000
% 0.46/0.66  #    Success case prop solver time     : 0.000
% 0.46/0.66  # Current number of processed clauses  : 339
% 0.46/0.66  #    Positive orientable unit clauses  : 24
% 0.46/0.66  #    Positive unorientable unit clauses: 1
% 0.46/0.66  #    Negative unit clauses             : 6
% 0.46/0.66  #    Non-unit-clauses                  : 308
% 0.46/0.66  # Current number of unprocessed clauses: 17303
% 0.46/0.66  # ...number of literals in the above   : 90300
% 0.46/0.66  # Current number of archived formulas  : 0
% 0.46/0.66  # Current number of archived clauses   : 92
% 0.46/0.66  # Clause-clause subsumption calls (NU) : 21022
% 0.46/0.66  # Rec. Clause-clause subsumption calls : 10922
% 0.46/0.66  # Non-unit clause-clause subsumptions  : 1133
% 0.46/0.66  # Unit Clause-clause subsumption calls : 117
% 0.46/0.66  # Rewrite failures with RHS unbound    : 0
% 0.46/0.66  # BW rewrite match attempts            : 50
% 0.46/0.66  # BW rewrite match successes           : 29
% 0.46/0.66  # Condensation attempts                : 0
% 0.46/0.66  # Condensation successes               : 0
% 0.46/0.66  # Termbank termtop insertions          : 573344
% 0.46/0.66  
% 0.46/0.66  # -------------------------------------------------
% 0.46/0.66  # User time                : 0.292 s
% 0.46/0.66  # System time              : 0.017 s
% 0.46/0.66  # Total time               : 0.309 s
% 0.46/0.66  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
