%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:41:43 EST 2020

% Result     : Theorem 13.28s
% Output     : CNFRefutation 13.28s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 381 expanded)
%              Number of clauses        :   47 ( 178 expanded)
%              Number of leaves         :   17 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  178 ( 699 expanded)
%              Number of equality atoms :   80 ( 333 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(d6_xboole_0,axiom,(
    ! [X1,X2] : k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(t51_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
     => r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(t50_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

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

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(l36_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l36_xboole_1)).

fof(t96_enumset1,axiom,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_enumset1)).

fof(t16_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(t81_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
     => r1_xboole_0(X2,k4_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(c_0_17,plain,(
    ! [X43] :
      ( ( r1_xboole_0(X43,X43)
        | X43 != k1_xboole_0 )
      & ( X43 = k1_xboole_0
        | ~ r1_xboole_0(X43,X43) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

fof(c_0_18,plain,(
    ! [X49] : k5_xboole_0(X49,X49) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

fof(c_0_19,plain,(
    ! [X16,X17] : k5_xboole_0(X16,X17) = k2_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X16)) ),
    inference(variable_rename,[status(thm)],[d6_xboole_0])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k3_xboole_0(X1,k1_tarski(X2)) = k1_tarski(X2)
       => r2_hidden(X2,X1) ) ),
    inference(assume_negation,[status(cth)],[t51_zfmisc_1])).

fof(c_0_21,plain,(
    ! [X40,X41,X42] : k3_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(k3_xboole_0(X40,X41),k3_xboole_0(X40,X42)) ),
    inference(variable_rename,[status(thm)],[t50_xboole_1])).

fof(c_0_22,plain,(
    ! [X39] : k3_xboole_0(X39,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_23,plain,(
    ! [X47,X48] :
      ( ( ~ r1_xboole_0(X47,X48)
        | k4_xboole_0(X47,X48) = X47 )
      & ( k4_xboole_0(X47,X48) != X47
        | r1_xboole_0(X47,X48) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

fof(c_0_24,plain,(
    ! [X18,X19,X21,X22,X23] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | r1_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_2(X18,X19),X19)
        | r1_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | ~ r1_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_25,plain,(
    ! [X24,X25,X27,X28,X29] :
      ( ( r1_xboole_0(X24,X25)
        | r2_hidden(esk3_2(X24,X25),k3_xboole_0(X24,X25)) )
      & ( ~ r2_hidden(X29,k3_xboole_0(X27,X28))
        | ~ r1_xboole_0(X27,X28) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X30,X31,X32] : k4_xboole_0(X30,k3_xboole_0(X31,X32)) = k2_xboole_0(k4_xboole_0(X30,X31),k4_xboole_0(X30,X32)) ),
    inference(variable_rename,[status(thm)],[l36_xboole_1])).

fof(c_0_30,negated_conjecture,
    ( k3_xboole_0(esk5_0,k1_tarski(esk6_0)) = k1_tarski(esk6_0)
    & ~ r2_hidden(esk6_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

fof(c_0_31,plain,(
    ! [X59] : k6_enumset1(X59,X59,X59,X59,X59,X59,X59,X59) = k1_tarski(X59) ),
    inference(variable_rename,[status(thm)],[t96_enumset1])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X36,X37,X38] : k3_xboole_0(k3_xboole_0(X36,X37),X38) = k3_xboole_0(X36,k3_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t16_xboole_1])).

cnf(c_0_41,negated_conjecture,
    ( k3_xboole_0(esk5_0,k1_tarski(esk6_0)) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X44,X45,X46] :
      ( ~ r1_xboole_0(X44,k4_xboole_0(X45,X46))
      | r1_xboole_0(X45,k4_xboole_0(X44,X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).

cnf(c_0_44,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_33])).

cnf(c_0_47,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X1,X1)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( k3_xboole_0(k3_xboole_0(X1,X2),X3) = k3_xboole_0(X1,k3_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)) = k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_42])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X2,k4_xboole_0(X1,X3))
    | ~ r1_xboole_0(X1,k4_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) = k3_xboole_0(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_52,plain,
    ( k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X2)))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( k3_xboole_0(esk5_0,k3_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1)) = k3_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,k1_xboole_0))
    | ~ r1_xboole_0(X3,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(esk5_0,k3_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))
    | ~ r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_35]),c_0_46])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_37])).

fof(c_0_59,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_57]),c_0_58])).

cnf(c_0_61,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_62,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_47]),c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_60])).

cnf(c_0_64,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_47]),c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_33]),c_0_33]),c_0_63])).

fof(c_0_66,plain,(
    ! [X60,X61] :
      ( ~ r1_xboole_0(k1_tarski(X60),X61)
      | ~ r2_hidden(X60,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

cnf(c_0_67,plain,
    ( k4_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X1))) = k4_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_68,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_69,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56,X57] :
      ( ( ~ r2_hidden(X53,X52)
        | X53 = X50
        | X53 = X51
        | X52 != k2_tarski(X50,X51) )
      & ( X54 != X50
        | r2_hidden(X54,X52)
        | X52 != k2_tarski(X50,X51) )
      & ( X54 != X51
        | r2_hidden(X54,X52)
        | X52 != k2_tarski(X50,X51) )
      & ( esk4_3(X55,X56,X57) != X55
        | ~ r2_hidden(esk4_3(X55,X56,X57),X57)
        | X57 = k2_tarski(X55,X56) )
      & ( esk4_3(X55,X56,X57) != X56
        | ~ r2_hidden(esk4_3(X55,X56,X57),X57)
        | X57 = k2_tarski(X55,X56) )
      & ( r2_hidden(esk4_3(X55,X56,X57),X57)
        | esk4_3(X55,X56,X57) = X55
        | esk4_3(X55,X56,X57) = X56
        | X57 = k2_tarski(X55,X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_70,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_53]),c_0_47])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_70,c_0_42])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(X1,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_71]),c_0_60])])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k4_xboole_0(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( r2_hidden(X1,k4_xboole_0(k2_tarski(X1,X2),X3))
    | r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 13.28/13.45  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 13.28/13.45  # and selection function SelectNegativeLiterals.
% 13.28/13.45  #
% 13.28/13.45  # Preprocessing time       : 0.028 s
% 13.28/13.45  # Presaturation interreduction done
% 13.28/13.45  
% 13.28/13.45  # Proof found!
% 13.28/13.45  # SZS status Theorem
% 13.28/13.45  # SZS output start CNFRefutation
% 13.28/13.45  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 13.28/13.45  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 13.28/13.45  fof(d6_xboole_0, axiom, ![X1, X2]:k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 13.28/13.45  fof(t51_zfmisc_1, conjecture, ![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 13.28/13.45  fof(t50_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_xboole_1)).
% 13.28/13.45  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 13.28/13.45  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.28/13.45  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.28/13.45  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 13.28/13.45  fof(l36_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l36_xboole_1)).
% 13.28/13.45  fof(t96_enumset1, axiom, ![X1]:k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_enumset1)).
% 13.28/13.45  fof(t16_xboole_1, axiom, ![X1, X2, X3]:k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 13.28/13.45  fof(t81_xboole_1, axiom, ![X1, X2, X3]:(r1_xboole_0(X1,k4_xboole_0(X2,X3))=>r1_xboole_0(X2,k4_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 13.28/13.45  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 13.28/13.45  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 13.28/13.45  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 13.28/13.45  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 13.28/13.45  fof(c_0_17, plain, ![X43]:((r1_xboole_0(X43,X43)|X43!=k1_xboole_0)&(X43=k1_xboole_0|~r1_xboole_0(X43,X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 13.28/13.45  fof(c_0_18, plain, ![X49]:k5_xboole_0(X49,X49)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 13.28/13.45  fof(c_0_19, plain, ![X16, X17]:k5_xboole_0(X16,X17)=k2_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X17,X16)), inference(variable_rename,[status(thm)],[d6_xboole_0])).
% 13.28/13.45  fof(c_0_20, negated_conjecture, ~(![X1, X2]:(k3_xboole_0(X1,k1_tarski(X2))=k1_tarski(X2)=>r2_hidden(X2,X1))), inference(assume_negation,[status(cth)],[t51_zfmisc_1])).
% 13.28/13.45  fof(c_0_21, plain, ![X40, X41, X42]:k3_xboole_0(X40,k4_xboole_0(X41,X42))=k4_xboole_0(k3_xboole_0(X40,X41),k3_xboole_0(X40,X42)), inference(variable_rename,[status(thm)],[t50_xboole_1])).
% 13.28/13.45  fof(c_0_22, plain, ![X39]:k3_xboole_0(X39,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 13.28/13.45  fof(c_0_23, plain, ![X47, X48]:((~r1_xboole_0(X47,X48)|k4_xboole_0(X47,X48)=X47)&(k4_xboole_0(X47,X48)!=X47|r1_xboole_0(X47,X48))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 13.28/13.45  fof(c_0_24, plain, ![X18, X19, X21, X22, X23]:(((r2_hidden(esk2_2(X18,X19),X18)|r1_xboole_0(X18,X19))&(r2_hidden(esk2_2(X18,X19),X19)|r1_xboole_0(X18,X19)))&(~r2_hidden(X23,X21)|~r2_hidden(X23,X22)|~r1_xboole_0(X21,X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 13.28/13.45  fof(c_0_25, plain, ![X24, X25, X27, X28, X29]:((r1_xboole_0(X24,X25)|r2_hidden(esk3_2(X24,X25),k3_xboole_0(X24,X25)))&(~r2_hidden(X29,k3_xboole_0(X27,X28))|~r1_xboole_0(X27,X28))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 13.28/13.45  cnf(c_0_26, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 13.28/13.45  cnf(c_0_27, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 13.28/13.45  cnf(c_0_28, plain, (k5_xboole_0(X1,X2)=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 13.28/13.45  fof(c_0_29, plain, ![X30, X31, X32]:k4_xboole_0(X30,k3_xboole_0(X31,X32))=k2_xboole_0(k4_xboole_0(X30,X31),k4_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[l36_xboole_1])).
% 13.28/13.45  fof(c_0_30, negated_conjecture, (k3_xboole_0(esk5_0,k1_tarski(esk6_0))=k1_tarski(esk6_0)&~r2_hidden(esk6_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 13.28/13.45  fof(c_0_31, plain, ![X59]:k6_enumset1(X59,X59,X59,X59,X59,X59,X59,X59)=k1_tarski(X59), inference(variable_rename,[status(thm)],[t96_enumset1])).
% 13.28/13.45  cnf(c_0_32, plain, (k3_xboole_0(X1,k4_xboole_0(X2,X3))=k4_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 13.28/13.45  cnf(c_0_33, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 13.28/13.45  cnf(c_0_34, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 13.28/13.45  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 13.28/13.45  cnf(c_0_36, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 13.28/13.45  cnf(c_0_37, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_26])).
% 13.28/13.45  cnf(c_0_38, plain, (k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 13.28/13.45  cnf(c_0_39, plain, (k4_xboole_0(X1,k3_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 13.28/13.45  fof(c_0_40, plain, ![X36, X37, X38]:k3_xboole_0(k3_xboole_0(X36,X37),X38)=k3_xboole_0(X36,k3_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t16_xboole_1])).
% 13.28/13.45  cnf(c_0_41, negated_conjecture, (k3_xboole_0(esk5_0,k1_tarski(esk6_0))=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 13.28/13.45  cnf(c_0_42, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 13.28/13.45  fof(c_0_43, plain, ![X44, X45, X46]:(~r1_xboole_0(X44,k4_xboole_0(X45,X46))|r1_xboole_0(X45,k4_xboole_0(X44,X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t81_xboole_1])])).
% 13.28/13.45  cnf(c_0_44, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k1_xboole_0))=k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 13.28/13.45  cnf(c_0_45, plain, (k4_xboole_0(X1,X2)=X1|r2_hidden(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 13.28/13.45  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_33])).
% 13.28/13.45  cnf(c_0_47, plain, (k4_xboole_0(X1,k3_xboole_0(X1,X1))=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 13.28/13.45  cnf(c_0_48, plain, (k3_xboole_0(k3_xboole_0(X1,X2),X3)=k3_xboole_0(X1,k3_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 13.28/13.45  cnf(c_0_49, negated_conjecture, (k3_xboole_0(esk5_0,k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0))=k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_42]), c_0_42])).
% 13.28/13.45  cnf(c_0_50, plain, (r1_xboole_0(X2,k4_xboole_0(X1,X3))|~r1_xboole_0(X1,k4_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 13.28/13.45  cnf(c_0_51, plain, (k4_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)=k3_xboole_0(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 13.28/13.45  cnf(c_0_52, plain, (k3_xboole_0(X1,k4_xboole_0(X2,k3_xboole_0(X2,k3_xboole_0(X1,X2))))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_32])).
% 13.28/13.45  cnf(c_0_53, negated_conjecture, (k3_xboole_0(esk5_0,k3_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1))=k3_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 13.28/13.45  cnf(c_0_54, plain, (r1_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X3,k1_xboole_0))|~r1_xboole_0(X3,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 13.28/13.45  cnf(c_0_55, negated_conjecture, (k3_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(esk5_0,k3_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 13.28/13.45  cnf(c_0_56, negated_conjecture, (r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))|~r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 13.28/13.45  cnf(c_0_57, negated_conjecture, (r1_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_35]), c_0_46])).
% 13.28/13.45  cnf(c_0_58, plain, (k4_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_37])).
% 13.28/13.45  fof(c_0_59, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 13.28/13.45  cnf(c_0_60, negated_conjecture, (r1_xboole_0(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_57]), c_0_58])).
% 13.28/13.45  cnf(c_0_61, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 13.28/13.45  cnf(c_0_62, plain, (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k4_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_47]), c_0_48])).
% 13.28/13.45  cnf(c_0_63, negated_conjecture, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_34, c_0_60])).
% 13.28/13.45  cnf(c_0_64, plain, (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,X2))=k4_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_47]), c_0_61])).
% 13.28/13.45  cnf(c_0_65, negated_conjecture, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_33]), c_0_33]), c_0_63])).
% 13.28/13.45  fof(c_0_66, plain, ![X60, X61]:(~r1_xboole_0(k1_tarski(X60),X61)|~r2_hidden(X60,X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 13.28/13.45  cnf(c_0_67, plain, (k4_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(X1,X1)))=k4_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 13.28/13.45  fof(c_0_68, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 13.28/13.45  fof(c_0_69, plain, ![X50, X51, X52, X53, X54, X55, X56, X57]:(((~r2_hidden(X53,X52)|(X53=X50|X53=X51)|X52!=k2_tarski(X50,X51))&((X54!=X50|r2_hidden(X54,X52)|X52!=k2_tarski(X50,X51))&(X54!=X51|r2_hidden(X54,X52)|X52!=k2_tarski(X50,X51))))&(((esk4_3(X55,X56,X57)!=X55|~r2_hidden(esk4_3(X55,X56,X57),X57)|X57=k2_tarski(X55,X56))&(esk4_3(X55,X56,X57)!=X56|~r2_hidden(esk4_3(X55,X56,X57),X57)|X57=k2_tarski(X55,X56)))&(r2_hidden(esk4_3(X55,X56,X57),X57)|(esk4_3(X55,X56,X57)=X55|esk4_3(X55,X56,X57)=X56)|X57=k2_tarski(X55,X56)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 13.28/13.45  cnf(c_0_70, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 13.28/13.45  cnf(c_0_71, negated_conjecture, (k4_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),esk5_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_53]), c_0_47])).
% 13.28/13.45  cnf(c_0_72, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 13.28/13.45  cnf(c_0_73, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 13.28/13.45  cnf(c_0_74, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[c_0_70, c_0_42])).
% 13.28/13.45  cnf(c_0_75, negated_conjecture, (r1_xboole_0(k6_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0),k4_xboole_0(X1,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_71]), c_0_60])])).
% 13.28/13.45  cnf(c_0_76, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_72])).
% 13.28/13.45  cnf(c_0_77, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_73])])).
% 13.28/13.45  cnf(c_0_78, negated_conjecture, (~r2_hidden(esk6_0,k4_xboole_0(X1,esk5_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 13.28/13.45  cnf(c_0_79, plain, (r2_hidden(X1,k4_xboole_0(k2_tarski(X1,X2),X3))|r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 13.28/13.45  cnf(c_0_80, negated_conjecture, (~r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 13.28/13.45  cnf(c_0_81, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), ['proof']).
% 13.28/13.45  # SZS output end CNFRefutation
% 13.28/13.45  # Proof object total steps             : 82
% 13.28/13.45  # Proof object clause steps            : 47
% 13.28/13.45  # Proof object formula steps           : 35
% 13.28/13.45  # Proof object conjectures             : 17
% 13.28/13.45  # Proof object clause conjectures      : 14
% 13.28/13.45  # Proof object formula conjectures     : 3
% 13.28/13.45  # Proof object initial clauses used    : 18
% 13.28/13.45  # Proof object initial formulas used   : 17
% 13.28/13.45  # Proof object generating inferences   : 21
% 13.28/13.45  # Proof object simplifying inferences  : 24
% 13.28/13.45  # Training examples: 0 positive, 0 negative
% 13.28/13.45  # Parsed axioms                        : 18
% 13.28/13.45  # Removed by relevancy pruning/SinE    : 0
% 13.28/13.45  # Initial clauses                      : 34
% 13.28/13.45  # Removed in clause preprocessing      : 2
% 13.28/13.45  # Initial clauses in saturation        : 32
% 13.28/13.45  # Processed clauses                    : 29962
% 13.28/13.45  # ...of these trivial                  : 1788
% 13.28/13.45  # ...subsumed                          : 25175
% 13.28/13.45  # ...remaining for further processing  : 2999
% 13.28/13.45  # Other redundant clauses eliminated   : 2513
% 13.28/13.45  # Clauses deleted for lack of memory   : 0
% 13.28/13.45  # Backward-subsumed                    : 58
% 13.28/13.45  # Backward-rewritten                   : 534
% 13.28/13.45  # Generated clauses                    : 2021495
% 13.28/13.45  # ...of the previous two non-trivial   : 1233735
% 13.28/13.45  # Contextual simplify-reflections      : 6
% 13.28/13.45  # Paramodulations                      : 2018749
% 13.28/13.45  # Factorizations                       : 232
% 13.28/13.45  # Equation resolutions                 : 2516
% 13.28/13.45  # Propositional unsat checks           : 0
% 13.28/13.45  #    Propositional check models        : 0
% 13.28/13.45  #    Propositional check unsatisfiable : 0
% 13.28/13.45  #    Propositional clauses             : 0
% 13.28/13.45  #    Propositional clauses after purity: 0
% 13.28/13.45  #    Propositional unsat core size     : 0
% 13.28/13.45  #    Propositional preprocessing time  : 0.000
% 13.28/13.45  #    Propositional encoding time       : 0.000
% 13.28/13.46  #    Propositional solver time         : 0.000
% 13.28/13.46  #    Success case prop preproc time    : 0.000
% 13.28/13.46  #    Success case prop encoding time   : 0.000
% 13.28/13.46  #    Success case prop solver time     : 0.000
% 13.28/13.46  # Current number of processed clauses  : 2368
% 13.28/13.46  #    Positive orientable unit clauses  : 697
% 13.28/13.46  #    Positive unorientable unit clauses: 2
% 13.28/13.46  #    Negative unit clauses             : 224
% 13.28/13.46  #    Non-unit-clauses                  : 1445
% 13.28/13.46  # Current number of unprocessed clauses: 1197372
% 13.28/13.46  # ...number of literals in the above   : 4677340
% 13.28/13.46  # Current number of archived formulas  : 0
% 13.28/13.46  # Current number of archived clauses   : 626
% 13.28/13.46  # Clause-clause subsumption calls (NU) : 887267
% 13.28/13.46  # Rec. Clause-clause subsumption calls : 543842
% 13.28/13.46  # Non-unit clause-clause subsumptions  : 4095
% 13.28/13.46  # Unit Clause-clause subsumption calls : 165340
% 13.28/13.46  # Rewrite failures with RHS unbound    : 0
% 13.28/13.46  # BW rewrite match attempts            : 6875
% 13.28/13.46  # BW rewrite match successes           : 352
% 13.28/13.46  # Condensation attempts                : 0
% 13.28/13.46  # Condensation successes               : 0
% 13.28/13.46  # Termbank termtop insertions          : 71951210
% 13.28/13.50  
% 13.28/13.50  # -------------------------------------------------
% 13.28/13.50  # User time                : 12.701 s
% 13.28/13.50  # System time              : 0.451 s
% 13.28/13.50  # Total time               : 13.152 s
% 13.28/13.50  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
