%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:06 EST 2020

% Result     : Theorem 6.22s
% Output     : CNFRefutation 6.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 507 expanded)
%              Number of clauses        :   40 ( 207 expanded)
%              Number of leaves         :   16 ( 146 expanded)
%              Depth                    :    9
%              Number of atoms          :  175 ( 719 expanded)
%              Number of equality atoms :   58 ( 471 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_ordinal1,conjecture,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(X1,X2)
        & r2_hidden(X3,k2_xboole_0(X1,X2))
        & ~ ( r2_hidden(X3,X1)
            & ~ r2_hidden(X3,X2) )
        & ~ ( r2_hidden(X3,X2)
            & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( r2_hidden(X1,k1_ordinal1(X2))
      <=> ( r2_hidden(X1,X2)
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t13_ordinal1])).

fof(c_0_17,plain,(
    ! [X41] : k1_ordinal1(X41) = k2_xboole_0(X41,k1_tarski(X41)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_18,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X37,X38] : k3_tarski(k2_tarski(X37,X38)) = k2_xboole_0(X37,X38) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,negated_conjecture,
    ( ( ~ r2_hidden(esk3_0,esk4_0)
      | ~ r2_hidden(esk3_0,k1_ordinal1(esk4_0)) )
    & ( esk3_0 != esk4_0
      | ~ r2_hidden(esk3_0,k1_ordinal1(esk4_0)) )
    & ( r2_hidden(esk3_0,k1_ordinal1(esk4_0))
      | r2_hidden(esk3_0,esk4_0)
      | esk3_0 = esk4_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).

cnf(c_0_22,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k1_enumset1(X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_27,plain,(
    ! [X33,X34,X35,X36] : k3_enumset1(X33,X33,X34,X35,X36) = k2_enumset1(X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_28,plain,(
    ! [X16,X17] : r1_tarski(X16,k2_xboole_0(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_29,plain,(
    ! [X39,X40] :
      ( ( k4_xboole_0(X39,k1_tarski(X40)) != X39
        | ~ r2_hidden(X40,X39) )
      & ( r2_hidden(X40,X39)
        | k4_xboole_0(X39,k1_tarski(X40)) = X39 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

cnf(c_0_30,negated_conjecture,
    ( esk3_0 != esk4_0
    | ~ r2_hidden(esk3_0,k1_ordinal1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk3_0,k1_ordinal1(esk4_0))
    | r2_hidden(esk3_0,esk4_0)
    | esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_36,plain,(
    ! [X42] : r2_hidden(X42,k1_ordinal1(X42)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

fof(c_0_37,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(X13,X12)
        | r2_hidden(X13,X11)
        | ~ r1_xboole_0(X11,X12)
        | ~ r2_hidden(X13,k2_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X11)
        | ~ r1_xboole_0(X11,X12)
        | ~ r2_hidden(X13,k2_xboole_0(X11,X12)) )
      & ( r2_hidden(X13,X12)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12)
        | ~ r2_hidden(X13,k2_xboole_0(X11,X12)) )
      & ( ~ r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | ~ r1_xboole_0(X11,X12)
        | ~ r2_hidden(X13,k2_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).

fof(c_0_40,plain,(
    ! [X18,X19] :
      ( ( ~ r1_xboole_0(X18,X19)
        | k4_xboole_0(X18,X19) = X18 )
      & ( k4_xboole_0(X18,X19) != X18
        | r1_xboole_0(X18,X19) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_42,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_43,negated_conjecture,
    ( esk4_0 != esk3_0
    | ~ r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_25]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_hidden(esk3_0,esk4_0)
    | r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_31]),c_0_25]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_32]),c_0_33]),c_0_34])).

fof(c_0_48,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk2_2(X24,X25),X25)
        | esk2_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r1_xboole_0(X3,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1)) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_23]),c_0_25]),c_0_33]),c_0_34])).

fof(c_0_52,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ r1_tarski(X44,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k1_ordinal1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))
    | r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk4_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_31]),c_0_25]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X2)
    | ~ r1_xboole_0(X3,X2)
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_60,plain,
    ( r1_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_31]),c_0_25]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])]),c_0_57])).

cnf(c_0_65,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_23]),c_0_25]),c_0_33]),c_0_34])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | r2_hidden(X2,X3)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X2,X2,X2,X2,X2)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_69,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_64]),c_0_67]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_64])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.10/0.29  % Computer   : n018.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % WCLimit    : 600
% 0.10/0.29  % DateTime   : Tue Dec  1 14:22:26 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  # Version: 2.5pre002
% 0.10/0.30  # No SInE strategy applied
% 0.10/0.30  # Trying AutoSched0 for 299 seconds
% 6.22/6.47  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 6.22/6.47  # and selection function SelectNegativeLiterals.
% 6.22/6.47  #
% 6.22/6.47  # Preprocessing time       : 0.027 s
% 6.22/6.47  # Presaturation interreduction done
% 6.22/6.47  
% 6.22/6.47  # Proof found!
% 6.22/6.47  # SZS status Theorem
% 6.22/6.47  # SZS output start CNFRefutation
% 6.22/6.47  fof(t13_ordinal1, conjecture, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 6.22/6.47  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.22/6.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.22/6.47  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.22/6.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.22/6.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.22/6.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.22/6.47  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.22/6.47  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 6.22/6.47  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 6.22/6.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.22/6.47  fof(t5_xboole_0, axiom, ![X1, X2, X3]:~((((r1_xboole_0(X1,X2)&r2_hidden(X3,k2_xboole_0(X1,X2)))&~((r2_hidden(X3,X1)&~(r2_hidden(X3,X2)))))&~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 6.22/6.47  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 6.22/6.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.22/6.47  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 6.22/6.47  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.22/6.47  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2))), inference(assume_negation,[status(cth)],[t13_ordinal1])).
% 6.22/6.47  fof(c_0_17, plain, ![X41]:k1_ordinal1(X41)=k2_xboole_0(X41,k1_tarski(X41)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 6.22/6.47  fof(c_0_18, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 6.22/6.47  fof(c_0_19, plain, ![X37, X38]:k3_tarski(k2_tarski(X37,X38))=k2_xboole_0(X37,X38), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 6.22/6.47  fof(c_0_20, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 6.22/6.47  fof(c_0_21, negated_conjecture, (((~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,k1_ordinal1(esk4_0)))&(esk3_0!=esk4_0|~r2_hidden(esk3_0,k1_ordinal1(esk4_0))))&(r2_hidden(esk3_0,k1_ordinal1(esk4_0))|(r2_hidden(esk3_0,esk4_0)|esk3_0=esk4_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])])).
% 6.22/6.47  cnf(c_0_22, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.22/6.47  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 6.22/6.47  cnf(c_0_24, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 6.22/6.47  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 6.22/6.47  fof(c_0_26, plain, ![X30, X31, X32]:k2_enumset1(X30,X30,X31,X32)=k1_enumset1(X30,X31,X32), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 6.22/6.47  fof(c_0_27, plain, ![X33, X34, X35, X36]:k3_enumset1(X33,X33,X34,X35,X36)=k2_enumset1(X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 6.22/6.47  fof(c_0_28, plain, ![X16, X17]:r1_tarski(X16,k2_xboole_0(X16,X17)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 6.22/6.47  fof(c_0_29, plain, ![X39, X40]:((k4_xboole_0(X39,k1_tarski(X40))!=X39|~r2_hidden(X40,X39))&(r2_hidden(X40,X39)|k4_xboole_0(X39,k1_tarski(X40))=X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 6.22/6.47  cnf(c_0_30, negated_conjecture, (esk3_0!=esk4_0|~r2_hidden(esk3_0,k1_ordinal1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.22/6.47  cnf(c_0_31, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 6.22/6.47  cnf(c_0_32, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 6.22/6.47  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 6.22/6.47  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 6.22/6.47  cnf(c_0_35, negated_conjecture, (r2_hidden(esk3_0,k1_ordinal1(esk4_0))|r2_hidden(esk3_0,esk4_0)|esk3_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.22/6.47  fof(c_0_36, plain, ![X42]:r2_hidden(X42,k1_ordinal1(X42)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 6.22/6.47  fof(c_0_37, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 6.22/6.47  cnf(c_0_38, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 6.22/6.47  fof(c_0_39, plain, ![X11, X12, X13]:(((r2_hidden(X13,X12)|(r2_hidden(X13,X11)|(~r1_xboole_0(X11,X12)|~r2_hidden(X13,k2_xboole_0(X11,X12)))))&(~r2_hidden(X13,X11)|(r2_hidden(X13,X11)|(~r1_xboole_0(X11,X12)|~r2_hidden(X13,k2_xboole_0(X11,X12))))))&((r2_hidden(X13,X12)|(~r2_hidden(X13,X12)|(~r1_xboole_0(X11,X12)|~r2_hidden(X13,k2_xboole_0(X11,X12)))))&(~r2_hidden(X13,X11)|(~r2_hidden(X13,X12)|(~r1_xboole_0(X11,X12)|~r2_hidden(X13,k2_xboole_0(X11,X12))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_xboole_0])])])])).
% 6.22/6.47  fof(c_0_40, plain, ![X18, X19]:((~r1_xboole_0(X18,X19)|k4_xboole_0(X18,X19)=X18)&(k4_xboole_0(X18,X19)!=X18|r1_xboole_0(X18,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 6.22/6.47  cnf(c_0_41, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_29])).
% 6.22/6.47  fof(c_0_42, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 6.22/6.47  cnf(c_0_43, negated_conjecture, (esk4_0!=esk3_0|~r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_25]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 6.22/6.47  cnf(c_0_44, negated_conjecture, (esk4_0=esk3_0|r2_hidden(esk3_0,esk4_0)|r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_31]), c_0_25]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 6.22/6.47  cnf(c_0_45, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 6.22/6.47  cnf(c_0_46, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 6.22/6.47  cnf(c_0_47, plain, (r1_tarski(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_32]), c_0_33]), c_0_34])).
% 6.22/6.47  fof(c_0_48, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|X22=X20|X21!=k1_tarski(X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_tarski(X20)))&((~r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)!=X24|X25=k1_tarski(X24))&(r2_hidden(esk2_2(X24,X25),X25)|esk2_2(X24,X25)=X24|X25=k1_tarski(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 6.22/6.47  cnf(c_0_49, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r1_xboole_0(X3,X2)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 6.22/6.47  cnf(c_0_50, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 6.22/6.47  cnf(c_0_51, plain, (k4_xboole_0(X2,k3_enumset1(X1,X1,X1,X1,X1))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_23]), c_0_25]), c_0_33]), c_0_34])).
% 6.22/6.47  fof(c_0_52, plain, ![X43, X44]:(~r2_hidden(X43,X44)|~r1_tarski(X44,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 6.22/6.47  cnf(c_0_53, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_42])).
% 6.22/6.47  cnf(c_0_54, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,k1_ordinal1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 6.22/6.47  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))|r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk4_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 6.22/6.47  cnf(c_0_56, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_31]), c_0_25]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 6.22/6.47  cnf(c_0_57, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 6.22/6.47  cnf(c_0_58, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 6.22/6.47  cnf(c_0_59, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X2)|~r1_xboole_0(X3,X2)|~r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_32]), c_0_33]), c_0_34])).
% 6.22/6.47  cnf(c_0_60, plain, (r1_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 6.22/6.47  cnf(c_0_61, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 6.22/6.47  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_53])).
% 6.22/6.47  cnf(c_0_63, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)|~r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_31]), c_0_25]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34])).
% 6.22/6.47  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_0,k3_tarski(k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])]), c_0_57])).
% 6.22/6.47  cnf(c_0_65, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_23]), c_0_25]), c_0_33]), c_0_34])).
% 6.22/6.47  cnf(c_0_66, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))|r2_hidden(X2,X3)|r2_hidden(X1,X3)|~r2_hidden(X1,k3_tarski(k3_enumset1(X3,X3,X3,X3,k3_enumset1(X2,X2,X2,X2,X2))))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 6.22/6.47  cnf(c_0_67, plain, (~r2_hidden(X1,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 6.22/6.47  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 6.22/6.47  cnf(c_0_69, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_65])).
% 6.22/6.47  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_0,k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_64]), c_0_67]), c_0_68])).
% 6.22/6.47  cnf(c_0_71, negated_conjecture, (esk3_0!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_64])])).
% 6.22/6.47  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), ['proof']).
% 6.22/6.47  # SZS output end CNFRefutation
% 6.22/6.47  # Proof object total steps             : 73
% 6.22/6.47  # Proof object clause steps            : 40
% 6.22/6.47  # Proof object formula steps           : 33
% 6.22/6.47  # Proof object conjectures             : 15
% 6.22/6.47  # Proof object clause conjectures      : 12
% 6.22/6.47  # Proof object formula conjectures     : 3
% 6.22/6.47  # Proof object initial clauses used    : 18
% 6.22/6.47  # Proof object initial formulas used   : 16
% 6.22/6.47  # Proof object generating inferences   : 7
% 6.22/6.47  # Proof object simplifying inferences  : 56
% 6.22/6.47  # Training examples: 0 positive, 0 negative
% 6.22/6.47  # Parsed axioms                        : 16
% 6.22/6.47  # Removed by relevancy pruning/SinE    : 0
% 6.22/6.47  # Initial clauses                      : 30
% 6.22/6.47  # Removed in clause preprocessing      : 8
% 6.22/6.47  # Initial clauses in saturation        : 22
% 6.22/6.47  # Processed clauses                    : 5584
% 6.22/6.47  # ...of these trivial                  : 7
% 6.22/6.47  # ...subsumed                          : 4186
% 6.22/6.47  # ...remaining for further processing  : 1391
% 6.22/6.47  # Other redundant clauses eliminated   : 2851
% 6.22/6.47  # Clauses deleted for lack of memory   : 0
% 6.22/6.47  # Backward-subsumed                    : 75
% 6.22/6.47  # Backward-rewritten                   : 13
% 6.22/6.47  # Generated clauses                    : 494310
% 6.22/6.47  # ...of the previous two non-trivial   : 473116
% 6.22/6.47  # Contextual simplify-reflections      : 14
% 6.22/6.47  # Paramodulations                      : 491276
% 6.22/6.47  # Factorizations                       : 184
% 6.22/6.47  # Equation resolutions                 : 2851
% 6.22/6.47  # Propositional unsat checks           : 0
% 6.22/6.47  #    Propositional check models        : 0
% 6.22/6.47  #    Propositional check unsatisfiable : 0
% 6.22/6.47  #    Propositional clauses             : 0
% 6.22/6.47  #    Propositional clauses after purity: 0
% 6.22/6.47  #    Propositional unsat core size     : 0
% 6.22/6.47  #    Propositional preprocessing time  : 0.000
% 6.22/6.47  #    Propositional encoding time       : 0.000
% 6.22/6.47  #    Propositional solver time         : 0.000
% 6.22/6.47  #    Success case prop preproc time    : 0.000
% 6.22/6.47  #    Success case prop encoding time   : 0.000
% 6.22/6.47  #    Success case prop solver time     : 0.000
% 6.22/6.47  # Current number of processed clauses  : 1278
% 6.22/6.47  #    Positive orientable unit clauses  : 20
% 6.22/6.47  #    Positive unorientable unit clauses: 0
% 6.22/6.47  #    Negative unit clauses             : 4
% 6.22/6.47  #    Non-unit-clauses                  : 1254
% 6.22/6.47  # Current number of unprocessed clauses: 467277
% 6.22/6.47  # ...number of literals in the above   : 3163134
% 6.22/6.47  # Current number of archived formulas  : 0
% 6.22/6.47  # Current number of archived clauses   : 115
% 6.22/6.47  # Clause-clause subsumption calls (NU) : 399157
% 6.22/6.47  # Rec. Clause-clause subsumption calls : 69183
% 6.22/6.47  # Non-unit clause-clause subsumptions  : 4056
% 6.22/6.47  # Unit Clause-clause subsumption calls : 376
% 6.22/6.47  # Rewrite failures with RHS unbound    : 0
% 6.22/6.47  # BW rewrite match attempts            : 413
% 6.22/6.47  # BW rewrite match successes           : 6
% 6.22/6.47  # Condensation attempts                : 0
% 6.22/6.47  # Condensation successes               : 0
% 6.22/6.47  # Termbank termtop insertions          : 19853514
% 6.34/6.49  
% 6.34/6.49  # -------------------------------------------------
% 6.34/6.49  # User time                : 5.993 s
% 6.34/6.49  # System time              : 0.204 s
% 6.34/6.49  # Total time               : 6.197 s
% 6.34/6.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
