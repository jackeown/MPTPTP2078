%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:39:55 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 (21881 expanded)
%              Number of clauses        :   62 (8926 expanded)
%              Number of leaves         :   15 (6292 expanded)
%              Depth                    :   24
%              Number of atoms          :  221 (37000 expanded)
%              Number of equality atoms :  129 (30293 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t43_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_xboole_0
            & X3 = k1_tarski(X1) )
        & ~ ( X2 = k1_tarski(X1)
            & X3 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(l45_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_tarski(X2,X3))
    <=> ~ ( X1 != k1_xboole_0
          & X1 != k1_tarski(X2)
          & X1 != k1_tarski(X3)
          & X1 != k2_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(c_0_15,plain,(
    ! [X46,X47] : k3_tarski(k2_tarski(X46,X47)) = k2_xboole_0(X46,X47) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X30,X31] : k1_enumset1(X30,X30,X31) = k2_tarski(X30,X31) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_xboole_0
              & X3 = k1_tarski(X1) )
          & ~ ( X2 = k1_tarski(X1)
              & X3 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t43_zfmisc_1])).

fof(c_0_18,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,X20)
      | k2_xboole_0(X19,X20) = X20 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_19,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X32,X33,X34] : k2_enumset1(X32,X32,X33,X34) = k1_enumset1(X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X35,X36,X37,X38] : k3_enumset1(X35,X35,X36,X37,X38) = k2_enumset1(X35,X36,X37,X38) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_xboole_0
      | esk6_0 != k1_tarski(esk4_0) )
    & ( esk5_0 != k1_tarski(esk4_0)
      | esk6_0 != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_24,plain,(
    ! [X29] : k2_tarski(X29,X29) = k1_tarski(X29) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_25,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X21] : r1_tarski(k1_xboole_0,X21) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_30,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(X8,X5)
        | r2_hidden(X8,X6)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k2_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k2_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_34,plain,
    ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_36,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(k2_xboole_0(X16,X17),X18)
      | r1_tarski(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

fof(c_0_37,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r1_tarski(X43,k2_tarski(X44,X45))
        | X43 = k1_xboole_0
        | X43 = k1_tarski(X44)
        | X43 = k1_tarski(X45)
        | X43 = k2_tarski(X44,X45) )
      & ( X43 != k1_xboole_0
        | r1_tarski(X43,k2_tarski(X44,X45)) )
      & ( X43 != k1_tarski(X44)
        | r1_tarski(X43,k2_tarski(X44,X45)) )
      & ( X43 != k1_tarski(X45)
        | r1_tarski(X43,k2_tarski(X44,X45)) )
      & ( X43 != k2_tarski(X44,X45)
        | r1_tarski(X43,k2_tarski(X44,X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_20]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,k2_tarski(X2,X3))
    | X1 != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X22
        | X23 != k1_tarski(X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_tarski(X22) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | esk3_2(X26,X27) != X26
        | X27 = k1_tarski(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | esk3_2(X26,X27) = X26
        | X27 = k1_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | esk6_0 != k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_32]),c_0_20]),c_0_27]),c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk6_0
    | r2_hidden(esk2_1(esk5_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

fof(c_0_49,plain,(
    ! [X41,X42] :
      ( ( ~ r1_tarski(X41,k1_tarski(X42))
        | X41 = k1_xboole_0
        | X41 = k1_tarski(X42) )
      & ( X41 != k1_xboole_0
        | r1_tarski(X41,k1_tarski(X42)) )
      & ( X41 != k1_tarski(X42)
        | r1_tarski(X41,k1_tarski(X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3))
    | X1 != k3_enumset1(X2,X2,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_20]),c_0_20]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_52,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_41])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | ~ r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_40])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_32]),c_0_20]),c_0_27]),c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | ~ r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_32]),c_0_32]),c_0_20]),c_0_20]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_40])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | esk5_0 != k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_32]),c_0_20]),c_0_27]),c_0_28])).

cnf(c_0_66,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk5_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( esk2_1(esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk4_0,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_41])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_1(esk6_0),esk6_0)
    | r2_hidden(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_42])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = X1
    | r2_hidden(esk2_1(esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_72])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk2_1(esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_74]),c_0_70]),c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_1(esk6_0),k3_tarski(k3_enumset1(X1,X1,X1,X1,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

fof(c_0_78,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | k2_xboole_0(k1_tarski(X39),X40) = X40 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk2_1(esk6_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_40])).

cnf(c_0_80,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( esk2_1(esk6_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_79])).

cnf(c_0_82,plain,
    ( k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),X2)) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_32]),c_0_20]),c_0_26]),c_0_27]),c_0_27]),c_0_27]),c_0_28]),c_0_28]),c_0_28]),c_0_28])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_76,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( esk5_0 != k1_tarski(esk4_0)
    | esk6_0 != k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_85,negated_conjecture,
    ( k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( esk5_0 != k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)
    | esk6_0 != k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_32]),c_0_32]),c_0_20]),c_0_20]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_87,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = esk6_0
    | esk5_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_66]),c_0_40])).

cnf(c_0_88,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk6_0 != esk5_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_66])).

cnf(c_0_89,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_87]),c_0_88])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk4_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_89]),c_0_89]),c_0_89]),c_0_89]),c_0_42])).

cnf(c_0_91,negated_conjecture,
    ( esk4_0 = X1 ),
    inference(spm,[status(thm)],[c_0_63,c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_89])]),c_0_91]),c_0_91])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:06:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.21/0.42  # and selection function SelectNegativeLiterals.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.045 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.21/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.42  fof(t43_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 0.21/0.42  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.21/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.42  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.21/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.42  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.21/0.42  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.21/0.42  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.21/0.42  fof(l45_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_tarski(X2,X3))<=>~((((X1!=k1_xboole_0&X1!=k1_tarski(X2))&X1!=k1_tarski(X3))&X1!=k2_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 0.21/0.42  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.42  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.21/0.42  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.21/0.42  fof(c_0_15, plain, ![X46, X47]:k3_tarski(k2_tarski(X46,X47))=k2_xboole_0(X46,X47), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.21/0.42  fof(c_0_16, plain, ![X30, X31]:k1_enumset1(X30,X30,X31)=k2_tarski(X30,X31), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.42  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&~((X2=k1_tarski(X1)&X3=k1_tarski(X1))))&~((X2=k1_xboole_0&X3=k1_tarski(X1))))&~((X2=k1_tarski(X1)&X3=k1_xboole_0))))), inference(assume_negation,[status(cth)],[t43_zfmisc_1])).
% 0.21/0.42  fof(c_0_18, plain, ![X19, X20]:(~r1_tarski(X19,X20)|k2_xboole_0(X19,X20)=X20), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.21/0.42  cnf(c_0_19, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.42  cnf(c_0_20, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.42  fof(c_0_21, plain, ![X32, X33, X34]:k2_enumset1(X32,X32,X33,X34)=k1_enumset1(X32,X33,X34), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.42  fof(c_0_22, plain, ![X35, X36, X37, X38]:k3_enumset1(X35,X35,X36,X37,X38)=k2_enumset1(X35,X36,X37,X38), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.21/0.42  fof(c_0_23, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)))&(esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.42  fof(c_0_24, plain, ![X29]:k2_tarski(X29,X29)=k1_tarski(X29), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.42  cnf(c_0_25, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.42  cnf(c_0_26, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.42  cnf(c_0_27, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_28, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  fof(c_0_29, plain, ![X21]:r1_tarski(k1_xboole_0,X21), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.42  fof(c_0_30, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.21/0.42  cnf(c_0_31, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.42  fof(c_0_33, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.21/0.42  cnf(c_0_34, plain, (k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))=X2|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.42  cnf(c_0_35, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.42  fof(c_0_36, plain, ![X16, X17, X18]:(~r1_tarski(k2_xboole_0(X16,X17),X18)|r1_tarski(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.21/0.42  fof(c_0_37, plain, ![X43, X44, X45]:((~r1_tarski(X43,k2_tarski(X44,X45))|(X43=k1_xboole_0|X43=k1_tarski(X44)|X43=k1_tarski(X45)|X43=k2_tarski(X44,X45)))&((((X43!=k1_xboole_0|r1_tarski(X43,k2_tarski(X44,X45)))&(X43!=k1_tarski(X44)|r1_tarski(X43,k2_tarski(X44,X45))))&(X43!=k1_tarski(X45)|r1_tarski(X43,k2_tarski(X44,X45))))&(X43!=k2_tarski(X44,X45)|r1_tarski(X43,k2_tarski(X44,X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l45_zfmisc_1])])])).
% 0.21/0.42  cnf(c_0_38, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.42  cnf(c_0_39, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_40, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_20]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.21/0.42  cnf(c_0_41, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.42  cnf(c_0_42, plain, (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X1))=X1), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.21/0.42  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  cnf(c_0_44, plain, (r1_tarski(X1,k2_tarski(X2,X3))|X1!=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.42  fof(c_0_45, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X24,X23)|X24=X22|X23!=k1_tarski(X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_tarski(X22)))&((~r2_hidden(esk3_2(X26,X27),X27)|esk3_2(X26,X27)!=X26|X27=k1_tarski(X26))&(r2_hidden(esk3_2(X26,X27),X27)|esk3_2(X26,X27)=X26|X27=k1_tarski(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.42  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.42  cnf(c_0_47, negated_conjecture, (esk5_0!=k1_xboole_0|esk6_0!=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_32]), c_0_20]), c_0_27]), c_0_28])).
% 0.21/0.42  cnf(c_0_48, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk6_0|r2_hidden(esk2_1(esk5_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.21/0.42  fof(c_0_49, plain, ![X41, X42]:((~r1_tarski(X41,k1_tarski(X42))|(X41=k1_xboole_0|X41=k1_tarski(X42)))&((X41!=k1_xboole_0|r1_tarski(X41,k1_tarski(X42)))&(X41!=k1_tarski(X42)|r1_tarski(X41,k1_tarski(X42))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.21/0.42  cnf(c_0_50, plain, (r1_tarski(X1,X3)|~r1_tarski(k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.42  cnf(c_0_51, plain, (r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X3))|X1!=k3_enumset1(X2,X2,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_20]), c_0_20]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.21/0.42  cnf(c_0_52, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.42  cnf(c_0_53, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_46])).
% 0.21/0.42  cnf(c_0_54, negated_conjecture, (r2_hidden(esk2_1(esk5_0),esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_41])).
% 0.21/0.42  cnf(c_0_55, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.42  cnf(c_0_56, negated_conjecture, (r1_tarski(esk5_0,X1)|~r1_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_50, c_0_40])).
% 0.21/0.42  cnf(c_0_57, plain, (r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2))), inference(er,[status(thm)],[c_0_51])).
% 0.21/0.42  cnf(c_0_58, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_32]), c_0_20]), c_0_27]), c_0_28])).
% 0.21/0.42  cnf(c_0_59, negated_conjecture, (r2_hidden(esk2_1(esk5_0),k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.42  cnf(c_0_60, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_61, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|~r1_tarski(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_32]), c_0_32]), c_0_20]), c_0_20]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.21/0.42  cnf(c_0_62, negated_conjecture, (r1_tarski(esk5_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.42  cnf(c_0_63, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_58])).
% 0.21/0.42  cnf(c_0_64, negated_conjecture, (r2_hidden(esk2_1(esk5_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_59, c_0_40])).
% 0.21/0.42  cnf(c_0_65, negated_conjecture, (esk6_0!=k1_xboole_0|esk5_0!=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_32]), c_0_20]), c_0_27]), c_0_28])).
% 0.21/0.42  cnf(c_0_66, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk5_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.42  cnf(c_0_67, negated_conjecture, (esk2_1(esk5_0)=esk4_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.42  cnf(c_0_68, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.42  cnf(c_0_69, negated_conjecture, (r2_hidden(esk4_0,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,X1)))), inference(rw,[status(thm)],[c_0_59, c_0_67])).
% 0.21/0.42  cnf(c_0_70, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_68, c_0_41])).
% 0.21/0.42  cnf(c_0_71, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.42  cnf(c_0_72, negated_conjecture, (r2_hidden(esk2_1(esk6_0),esk6_0)|r2_hidden(esk4_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_42])).
% 0.21/0.42  cnf(c_0_73, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.42  cnf(c_0_74, negated_conjecture, (esk4_0=X1|r2_hidden(esk2_1(esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_72])).
% 0.21/0.42  cnf(c_0_75, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_73])).
% 0.21/0.42  cnf(c_0_76, negated_conjecture, (r2_hidden(esk2_1(esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_74]), c_0_70]), c_0_74])).
% 0.21/0.42  cnf(c_0_77, negated_conjecture, (r2_hidden(esk2_1(esk6_0),k3_tarski(k3_enumset1(X1,X1,X1,X1,esk6_0)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.21/0.42  fof(c_0_78, plain, ![X39, X40]:(~r2_hidden(X39,X40)|k2_xboole_0(k1_tarski(X39),X40)=X40), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.21/0.42  cnf(c_0_79, negated_conjecture, (r2_hidden(esk2_1(esk6_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_77, c_0_40])).
% 0.21/0.42  cnf(c_0_80, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.21/0.42  cnf(c_0_81, negated_conjecture, (esk2_1(esk6_0)=esk4_0), inference(spm,[status(thm)],[c_0_63, c_0_79])).
% 0.21/0.42  cnf(c_0_82, plain, (k3_tarski(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),X2))=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_32]), c_0_20]), c_0_26]), c_0_27]), c_0_27]), c_0_27]), c_0_28]), c_0_28]), c_0_28]), c_0_28])).
% 0.21/0.42  cnf(c_0_83, negated_conjecture, (r2_hidden(esk4_0,esk6_0)), inference(rw,[status(thm)],[c_0_76, c_0_81])).
% 0.21/0.42  cnf(c_0_84, negated_conjecture, (esk5_0!=k1_tarski(esk4_0)|esk6_0!=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.42  cnf(c_0_85, negated_conjecture, (k3_tarski(k3_enumset1(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0),esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.21/0.42  cnf(c_0_86, negated_conjecture, (esk5_0!=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)|esk6_0!=k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_32]), c_0_32]), c_0_20]), c_0_20]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.21/0.42  cnf(c_0_87, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=esk6_0|esk5_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_66]), c_0_40])).
% 0.21/0.42  cnf(c_0_88, negated_conjecture, (esk5_0=k1_xboole_0|esk6_0!=esk5_0), inference(spm,[status(thm)],[c_0_86, c_0_66])).
% 0.21/0.42  cnf(c_0_89, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_87]), c_0_88])).
% 0.21/0.42  cnf(c_0_90, negated_conjecture, (r2_hidden(esk4_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_89]), c_0_89]), c_0_89]), c_0_89]), c_0_42])).
% 0.21/0.42  cnf(c_0_91, negated_conjecture, (esk4_0=X1), inference(spm,[status(thm)],[c_0_63, c_0_90])).
% 0.21/0.42  cnf(c_0_92, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_89])]), c_0_91]), c_0_91])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 93
% 0.21/0.42  # Proof object clause steps            : 62
% 0.21/0.42  # Proof object formula steps           : 31
% 0.21/0.42  # Proof object conjectures             : 36
% 0.21/0.42  # Proof object clause conjectures      : 33
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 19
% 0.21/0.42  # Proof object initial formulas used   : 15
% 0.21/0.42  # Proof object generating inferences   : 22
% 0.21/0.42  # Proof object simplifying inferences  : 87
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 15
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 32
% 0.21/0.42  # Removed in clause preprocessing      : 5
% 0.21/0.42  # Initial clauses in saturation        : 27
% 0.21/0.42  # Processed clauses                    : 178
% 0.21/0.42  # ...of these trivial                  : 12
% 0.21/0.42  # ...subsumed                          : 32
% 0.21/0.42  # ...remaining for further processing  : 133
% 0.21/0.42  # Other redundant clauses eliminated   : 63
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 5
% 0.21/0.42  # Backward-rewritten                   : 90
% 0.21/0.42  # Generated clauses                    : 1372
% 0.21/0.42  # ...of the previous two non-trivial   : 1130
% 0.21/0.42  # Contextual simplify-reflections      : 6
% 0.21/0.42  # Paramodulations                      : 1310
% 0.21/0.42  # Factorizations                       : 0
% 0.21/0.42  # Equation resolutions                 : 63
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 3
% 0.21/0.42  #    Positive orientable unit clauses  : 2
% 0.21/0.42  #    Positive unorientable unit clauses: 1
% 0.21/0.42  #    Negative unit clauses             : 0
% 0.21/0.42  #    Non-unit-clauses                  : 0
% 0.21/0.42  # Current number of unprocessed clauses: 916
% 0.21/0.42  # ...number of literals in the above   : 2825
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 124
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 266
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 220
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 39
% 0.21/0.42  # Unit Clause-clause subsumption calls : 61
% 0.21/0.42  # Rewrite failures with RHS unbound    : 3
% 0.21/0.42  # BW rewrite match attempts            : 66
% 0.21/0.42  # BW rewrite match successes           : 41
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 16855
% 0.21/0.42  
% 0.21/0.42  # -------------------------------------------------
% 0.21/0.42  # User time                : 0.074 s
% 0.21/0.42  # System time              : 0.007 s
% 0.21/0.42  # Total time               : 0.081 s
% 0.21/0.42  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
