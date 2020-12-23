%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:11 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   98 (1219 expanded)
%              Number of clauses        :   77 ( 554 expanded)
%              Number of leaves         :   10 ( 330 expanded)
%              Depth                    :   19
%              Number of atoms          :  300 (2966 expanded)
%              Number of equality atoms :  147 (1462 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(t64_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    <=> ( r2_hidden(X1,X2)
        & X1 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(t11_setfam_1,conjecture,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_10,plain,(
    ! [X26,X27] :
      ( ( ~ r1_tarski(X26,k1_tarski(X27))
        | X26 = k1_xboole_0
        | X26 = k1_tarski(X27) )
      & ( X26 != k1_xboole_0
        | r1_tarski(X26,k1_tarski(X27)) )
      & ( X26 != k1_tarski(X27)
        | r1_tarski(X26,k1_tarski(X27)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_11,plain,(
    ! [X20] : k2_tarski(X20,X20) = k1_tarski(X20) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X21,X22] : k1_enumset1(X21,X21,X22) = k2_tarski(X21,X22) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X23,X24,X25] : k2_enumset1(X23,X23,X24,X25) = k1_enumset1(X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk2_2(X17,X18),X18)
        | esk2_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X31,X32,X33,X34,X35,X37,X40,X41,X42,X43] :
      ( ( ~ r2_hidden(X33,X32)
        | ~ r2_hidden(X34,X31)
        | r2_hidden(X33,X34)
        | X32 != k1_setfam_1(X31)
        | X31 = k1_xboole_0 )
      & ( r2_hidden(esk3_3(X31,X32,X35),X31)
        | r2_hidden(X35,X32)
        | X32 != k1_setfam_1(X31)
        | X31 = k1_xboole_0 )
      & ( ~ r2_hidden(X35,esk3_3(X31,X32,X35))
        | r2_hidden(X35,X32)
        | X32 != k1_setfam_1(X31)
        | X31 = k1_xboole_0 )
      & ( r2_hidden(esk5_2(X31,X37),X31)
        | ~ r2_hidden(esk4_2(X31,X37),X37)
        | X37 = k1_setfam_1(X31)
        | X31 = k1_xboole_0 )
      & ( ~ r2_hidden(esk4_2(X31,X37),esk5_2(X31,X37))
        | ~ r2_hidden(esk4_2(X31,X37),X37)
        | X37 = k1_setfam_1(X31)
        | X31 = k1_xboole_0 )
      & ( r2_hidden(esk4_2(X31,X37),X37)
        | ~ r2_hidden(X40,X31)
        | r2_hidden(esk4_2(X31,X37),X40)
        | X37 = k1_setfam_1(X31)
        | X31 = k1_xboole_0 )
      & ( X42 != k1_setfam_1(X41)
        | X42 = k1_xboole_0
        | X41 != k1_xboole_0 )
      & ( X43 != k1_xboole_0
        | X43 = k1_setfam_1(X41)
        | X41 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] :
      ( ( r2_hidden(X28,X29)
        | ~ r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) )
      & ( X28 != X30
        | ~ r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) )
      & ( ~ r2_hidden(X28,X29)
        | X28 = X30
        | r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).

cnf(c_0_22,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | X3 != k1_xboole_0
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,esk1_2(X1,X3))
    | r1_tarski(X1,X3)
    | X4 != k1_setfam_1(X1)
    | ~ r2_hidden(X2,X4) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( X1 = X3
    | r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_17]),c_0_18]),c_0_19])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(assume_negation,[status(cth)],[t11_setfam_1])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_enumset1(X3,X3,X3,X3))
    | r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X2,X3),esk1_2(X1,X4))
    | r1_tarski(X2,X3)
    | r1_tarski(X1,X4)
    | X2 != k1_setfam_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_37,plain,
    ( esk1_2(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))) = X3
    | r1_tarski(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))
    | ~ r2_hidden(esk1_2(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_39,negated_conjecture,(
    k1_setfam_1(k1_tarski(esk6_0)) != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).

cnf(c_0_40,plain,
    ( esk1_2(X1,X2) = X3
    | r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,esk1_2(X1,X3))
    | r1_tarski(X1,X3)
    | X2 != k1_setfam_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_36])).

cnf(c_0_42,plain,
    ( esk1_2(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) = X2
    | r1_tarski(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( k1_setfam_1(k1_tarski(esk6_0)) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( X1 = X2
    | r1_tarski(X3,X4)
    | X3 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_40])).

cnf(c_0_46,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_47,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
    | r1_tarski(X3,X2)
    | X3 != k1_setfam_1(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)
    | r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_50,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) != esk6_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_51,plain,
    ( X1 = X2
    | r1_tarski(k1_xboole_0,X3) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( X1 != X2
    | ~ r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = X1
    | X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_56])).

cnf(c_0_61,plain,
    ( esk2_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_64,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_65,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | esk2_2(X1,k1_xboole_0) = X1
    | r2_hidden(esk2_2(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_setfam_1(X1),esk1_2(X1,X2))
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_62,c_0_26])).

cnf(c_0_67,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_17]),c_0_17]),c_0_18]),c_0_18]),c_0_19]),c_0_19])).

cnf(c_0_69,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk2_2(X1,X2) != X1
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_70,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | esk2_2(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_58,c_0_65])).

cnf(c_0_71,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_72,plain,
    ( esk1_2(X1,X2) = k1_setfam_1(X1)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(esk1_2(X1,X2),k1_setfam_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_66]),c_0_45])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk3_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,plain,
    ( esk3_3(k2_enumset1(X1,X1,X1,X1),X2,X3) = X1
    | k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r2_hidden(X3,X2)
    | X2 != k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_67])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(X2,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_42])).

cnf(c_0_76,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(X1,X1,X1,X1)
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_55])).

cnf(c_0_77,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_79,plain,
    ( X1 = k1_setfam_1(X2)
    | r1_tarski(X2,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))
    | ~ r1_tarski(X1,k1_setfam_1(X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_42])).

cnf(c_0_80,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r2_hidden(X2,X3)
    | X3 != k1_setfam_1(k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))
    | r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_75])).

cnf(c_0_82,plain,
    ( k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)) = k1_xboole_0
    | k2_enumset1(X1,X1,X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_77]),c_0_60])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_enumset1(X1,X1,X1,X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,plain,
    ( k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)) = X1
    | X2 = k1_setfam_1(X1)
    | ~ r1_tarski(X2,k1_setfam_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_79]),c_0_55])])).

cnf(c_0_86,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r2_hidden(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | ~ r2_hidden(X2,X1) ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | k2_enumset1(X2,X2,X2,X2) != k1_xboole_0
    | ~ r2_hidden(X3,k2_enumset1(X2,X2,X2,X2)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_88,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[c_0_84])).

cnf(c_0_89,plain,
    ( X1 = k1_setfam_1(X2)
    | ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X1,k1_setfam_1(X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_85])).

cnf(c_0_90,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))
    | ~ r2_hidden(esk1_2(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_86])).

cnf(c_0_91,plain,
    ( X1 = X2
    | k2_enumset1(X3,X3,X3,X3) != k1_xboole_0
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X3)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_82]),c_0_83])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))
    | k2_enumset1(X2,X2,X2,X2) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1
    | ~ r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_88])).

cnf(c_0_94,plain,
    ( k2_enumset1(X1,X1,X1,X1) = k1_xboole_0
    | r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))) ),
    inference(spm,[status(thm)],[c_0_90,c_0_26])).

cnf(c_0_95,plain,
    ( X1 = X2
    | k2_enumset1(X3,X3,X3,X3) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.50/0.67  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.50/0.67  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.50/0.67  #
% 0.50/0.67  # Preprocessing time       : 0.028 s
% 0.50/0.67  # Presaturation interreduction done
% 0.50/0.67  
% 0.50/0.67  # Proof found!
% 0.50/0.67  # SZS status Theorem
% 0.50/0.67  # SZS output start CNFRefutation
% 0.50/0.67  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.50/0.67  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.50/0.67  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.50/0.67  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.50/0.67  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.50/0.67  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.50/0.67  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.50/0.67  fof(t64_zfmisc_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))<=>(r2_hidden(X1,X2)&X1!=X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 0.50/0.67  fof(t11_setfam_1, conjecture, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.50/0.67  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.50/0.67  fof(c_0_10, plain, ![X26, X27]:((~r1_tarski(X26,k1_tarski(X27))|(X26=k1_xboole_0|X26=k1_tarski(X27)))&((X26!=k1_xboole_0|r1_tarski(X26,k1_tarski(X27)))&(X26!=k1_tarski(X27)|r1_tarski(X26,k1_tarski(X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.50/0.67  fof(c_0_11, plain, ![X20]:k2_tarski(X20,X20)=k1_tarski(X20), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.50/0.67  fof(c_0_12, plain, ![X21, X22]:k1_enumset1(X21,X21,X22)=k2_tarski(X21,X22), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.50/0.67  fof(c_0_13, plain, ![X23, X24, X25]:k2_enumset1(X23,X23,X24,X25)=k1_enumset1(X23,X24,X25), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.50/0.67  fof(c_0_14, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X15,X14)|X15=X13|X14!=k1_tarski(X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k1_tarski(X13)))&((~r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)!=X17|X18=k1_tarski(X17))&(r2_hidden(esk2_2(X17,X18),X18)|esk2_2(X17,X18)=X17|X18=k1_tarski(X17)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.50/0.67  fof(c_0_15, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.50/0.67  cnf(c_0_16, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.50/0.67  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.50/0.67  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.50/0.67  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.50/0.67  fof(c_0_20, plain, ![X31, X32, X33, X34, X35, X37, X40, X41, X42, X43]:((((~r2_hidden(X33,X32)|(~r2_hidden(X34,X31)|r2_hidden(X33,X34))|X32!=k1_setfam_1(X31)|X31=k1_xboole_0)&((r2_hidden(esk3_3(X31,X32,X35),X31)|r2_hidden(X35,X32)|X32!=k1_setfam_1(X31)|X31=k1_xboole_0)&(~r2_hidden(X35,esk3_3(X31,X32,X35))|r2_hidden(X35,X32)|X32!=k1_setfam_1(X31)|X31=k1_xboole_0)))&(((r2_hidden(esk5_2(X31,X37),X31)|~r2_hidden(esk4_2(X31,X37),X37)|X37=k1_setfam_1(X31)|X31=k1_xboole_0)&(~r2_hidden(esk4_2(X31,X37),esk5_2(X31,X37))|~r2_hidden(esk4_2(X31,X37),X37)|X37=k1_setfam_1(X31)|X31=k1_xboole_0))&(r2_hidden(esk4_2(X31,X37),X37)|(~r2_hidden(X40,X31)|r2_hidden(esk4_2(X31,X37),X40))|X37=k1_setfam_1(X31)|X31=k1_xboole_0)))&((X42!=k1_setfam_1(X41)|X42=k1_xboole_0|X41!=k1_xboole_0)&(X43!=k1_xboole_0|X43=k1_setfam_1(X41)|X41!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.50/0.67  fof(c_0_21, plain, ![X28, X29, X30]:(((r2_hidden(X28,X29)|~r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))))&(X28!=X30|~r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30)))))&(~r2_hidden(X28,X29)|X28=X30|r2_hidden(X28,k4_xboole_0(X29,k1_tarski(X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_zfmisc_1])])])).
% 0.50/0.67  cnf(c_0_22, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.67  cnf(c_0_23, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.67  cnf(c_0_24, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  cnf(c_0_25, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.67  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.67  cnf(c_0_27, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.67  cnf(c_0_28, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  cnf(c_0_29, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|X3!=k1_xboole_0|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.50/0.67  cnf(c_0_30, plain, (X1=k1_xboole_0|r2_hidden(X2,esk1_2(X1,X3))|r1_tarski(X1,X3)|X4!=k1_setfam_1(X1)|~r2_hidden(X2,X4)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.50/0.67  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.50/0.67  cnf(c_0_32, plain, (X1=X3|r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  fof(c_0_33, negated_conjecture, ~(![X1]:k1_setfam_1(k1_tarski(X1))=X1), inference(assume_negation,[status(cth)],[t11_setfam_1])).
% 0.50/0.67  cnf(c_0_34, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_28])).
% 0.50/0.67  cnf(c_0_35, plain, (r2_hidden(esk1_2(X1,X2),k2_enumset1(X3,X3,X3,X3))|r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_26])).
% 0.50/0.67  cnf(c_0_36, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X2,X3),esk1_2(X1,X4))|r1_tarski(X2,X3)|r1_tarski(X1,X4)|X2!=k1_setfam_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.50/0.67  cnf(c_0_37, plain, (esk1_2(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))=X3|r1_tarski(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))|~r2_hidden(esk1_2(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3))),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.50/0.67  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k1_tarski(X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.67  fof(c_0_39, negated_conjecture, k1_setfam_1(k1_tarski(esk6_0))!=esk6_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_33])])])).
% 0.50/0.67  cnf(c_0_40, plain, (esk1_2(X1,X2)=X3|r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.50/0.67  cnf(c_0_41, plain, (X1=k1_xboole_0|r1_tarski(X2,esk1_2(X1,X3))|r1_tarski(X1,X3)|X2!=k1_setfam_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_36])).
% 0.50/0.67  cnf(c_0_42, plain, (esk1_2(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))=X2|r1_tarski(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_26])).
% 0.50/0.67  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  cnf(c_0_44, negated_conjecture, (k1_setfam_1(k1_tarski(esk6_0))!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.50/0.67  cnf(c_0_45, plain, (X1=X2|r1_tarski(X3,X4)|X3!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_40])).
% 0.50/0.67  cnf(c_0_46, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.50/0.67  fof(c_0_47, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.50/0.67  cnf(c_0_48, plain, (X1=k1_xboole_0|r1_tarski(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))|r1_tarski(X3,X2)|X3!=k1_setfam_1(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.50/0.67  cnf(c_0_49, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3),X1)|r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X3)), inference(spm,[status(thm)],[c_0_43, c_0_26])).
% 0.50/0.67  cnf(c_0_50, negated_conjecture, (k1_setfam_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))!=esk6_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  cnf(c_0_51, plain, (X1=X2|r1_tarski(k1_xboole_0,X3)), inference(er,[status(thm)],[c_0_45])).
% 0.50/0.67  cnf(c_0_52, plain, (X1!=X2|~r2_hidden(X1,k4_xboole_0(X3,k2_enumset1(X2,X2,X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.50/0.67  cnf(c_0_54, plain, (X1=k1_xboole_0|r1_tarski(X1,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))|r1_tarski(k1_setfam_1(X1),X2)), inference(er,[status(thm)],[c_0_48])).
% 0.50/0.67  cnf(c_0_55, plain, (r1_tarski(k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)),X1)), inference(spm,[status(thm)],[c_0_31, c_0_49])).
% 0.50/0.67  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_xboole_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_51])).
% 0.50/0.67  cnf(c_0_57, plain, (r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.67  cnf(c_0_58, plain, (~r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(er,[status(thm)],[c_0_52])).
% 0.50/0.67  cnf(c_0_59, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=X1|X1=k1_xboole_0|r1_tarski(k1_setfam_1(X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.50/0.67  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_23, c_0_56])).
% 0.50/0.67  cnf(c_0_61, plain, (esk2_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  cnf(c_0_62, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.50/0.67  cnf(c_0_63, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.50/0.67  cnf(c_0_64, plain, (X2=k1_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.67  cnf(c_0_65, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|esk2_2(X1,k1_xboole_0)=X1|r2_hidden(esk2_2(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.50/0.67  cnf(c_0_66, plain, (X1=k1_xboole_0|r1_tarski(k1_setfam_1(X1),esk1_2(X1,X2))|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_62, c_0_26])).
% 0.50/0.67  cnf(c_0_67, plain, (r2_hidden(esk3_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.67  cnf(c_0_68, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_17]), c_0_17]), c_0_18]), c_0_18]), c_0_19]), c_0_19])).
% 0.50/0.67  cnf(c_0_69, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk2_2(X1,X2)!=X1|~r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  cnf(c_0_70, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|esk2_2(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_58, c_0_65])).
% 0.50/0.67  cnf(c_0_71, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.50/0.67  cnf(c_0_72, plain, (esk1_2(X1,X2)=k1_setfam_1(X1)|r1_tarski(X1,X2)|~r1_tarski(esk1_2(X1,X2),k1_setfam_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_66]), c_0_45])).
% 0.50/0.67  cnf(c_0_73, plain, (r2_hidden(X1,X3)|X2=k1_xboole_0|~r2_hidden(X1,esk3_3(X2,X3,X1))|X3!=k1_setfam_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.50/0.67  cnf(c_0_74, plain, (esk3_3(k2_enumset1(X1,X1,X1,X1),X2,X3)=X1|k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r2_hidden(X3,X2)|X2!=k1_setfam_1(k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_34, c_0_67])).
% 0.50/0.67  cnf(c_0_75, plain, (r2_hidden(X1,X2)|r1_tarski(X2,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_26, c_0_42])).
% 0.50/0.67  cnf(c_0_76, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k2_enumset1(X1,X1,X1,X1)|k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_55])).
% 0.50/0.67  cnf(c_0_77, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.50/0.67  cnf(c_0_78, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_17]), c_0_18]), c_0_19])).
% 0.50/0.67  cnf(c_0_79, plain, (X1=k1_setfam_1(X2)|r1_tarski(X2,k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)))|~r1_tarski(X1,k1_setfam_1(X2))), inference(spm,[status(thm)],[c_0_72, c_0_42])).
% 0.50/0.67  cnf(c_0_80, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r2_hidden(X2,X3)|X3!=k1_setfam_1(k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.50/0.67  cnf(c_0_81, plain, (r2_hidden(X1,k4_xboole_0(X2,k2_enumset1(X3,X3,X3,X3)))|r2_hidden(X3,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_23, c_0_75])).
% 0.50/0.67  cnf(c_0_82, plain, (k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))=k1_xboole_0|k2_enumset1(X1,X1,X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_76])).
% 0.50/0.67  cnf(c_0_83, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_77]), c_0_60])).
% 0.50/0.67  cnf(c_0_84, plain, (r2_hidden(X1,X2)|X2!=k2_enumset1(X1,X1,X1,X1)), inference(er,[status(thm)],[c_0_78])).
% 0.50/0.67  cnf(c_0_85, plain, (k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))=X1|X2=k1_setfam_1(X1)|~r1_tarski(X2,k1_setfam_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_79]), c_0_55])])).
% 0.50/0.67  cnf(c_0_86, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r2_hidden(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))|~r2_hidden(X2,X1)), inference(er,[status(thm)],[c_0_80])).
% 0.50/0.67  cnf(c_0_87, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|k2_enumset1(X2,X2,X2,X2)!=k1_xboole_0|~r2_hidden(X3,k2_enumset1(X2,X2,X2,X2))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 0.50/0.67  cnf(c_0_88, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[c_0_84])).
% 0.50/0.67  cnf(c_0_89, plain, (X1=k1_setfam_1(X2)|~r2_hidden(X1,X2)|~r1_tarski(X1,k1_setfam_1(X2))), inference(spm,[status(thm)],[c_0_58, c_0_85])).
% 0.50/0.67  cnf(c_0_90, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r1_tarski(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))|~r2_hidden(esk1_2(X2,k1_setfam_1(k2_enumset1(X1,X1,X1,X1))),X1)), inference(spm,[status(thm)],[c_0_31, c_0_86])).
% 0.50/0.67  cnf(c_0_91, plain, (X1=X2|k2_enumset1(X3,X3,X3,X3)!=k1_xboole_0|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X3))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_82]), c_0_83])).
% 0.50/0.67  cnf(c_0_92, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))|k2_enumset1(X2,X2,X2,X2)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.50/0.67  cnf(c_0_93, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1|~r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_89, c_0_88])).
% 0.50/0.67  cnf(c_0_94, plain, (k2_enumset1(X1,X1,X1,X1)=k1_xboole_0|r1_tarski(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X1)))), inference(spm,[status(thm)],[c_0_90, c_0_26])).
% 0.50/0.67  cnf(c_0_95, plain, (X1=X2|k2_enumset1(X3,X3,X3,X3)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.50/0.67  cnf(c_0_96, plain, (k1_setfam_1(k2_enumset1(X1,X1,X1,X1))=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])).
% 0.50/0.67  cnf(c_0_97, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_96])]), ['proof']).
% 0.50/0.67  # SZS output end CNFRefutation
% 0.50/0.67  # Proof object total steps             : 98
% 0.50/0.67  # Proof object clause steps            : 77
% 0.50/0.67  # Proof object formula steps           : 21
% 0.50/0.67  # Proof object conjectures             : 12
% 0.50/0.67  # Proof object clause conjectures      : 9
% 0.50/0.67  # Proof object formula conjectures     : 3
% 0.50/0.67  # Proof object initial clauses used    : 20
% 0.50/0.67  # Proof object initial formulas used   : 10
% 0.50/0.67  # Proof object generating inferences   : 44
% 0.50/0.67  # Proof object simplifying inferences  : 47
% 0.50/0.67  # Training examples: 0 positive, 0 negative
% 0.50/0.67  # Parsed axioms                        : 10
% 0.50/0.67  # Removed by relevancy pruning/SinE    : 0
% 0.50/0.67  # Initial clauses                      : 28
% 0.50/0.67  # Removed in clause preprocessing      : 3
% 0.50/0.67  # Initial clauses in saturation        : 25
% 0.50/0.67  # Processed clauses                    : 1600
% 0.50/0.67  # ...of these trivial                  : 44
% 0.50/0.67  # ...subsumed                          : 999
% 0.50/0.67  # ...remaining for further processing  : 557
% 0.50/0.67  # Other redundant clauses eliminated   : 134
% 0.50/0.67  # Clauses deleted for lack of memory   : 0
% 0.50/0.67  # Backward-subsumed                    : 51
% 0.50/0.67  # Backward-rewritten                   : 108
% 0.50/0.67  # Generated clauses                    : 14392
% 0.50/0.67  # ...of the previous two non-trivial   : 12941
% 0.50/0.67  # Contextual simplify-reflections      : 106
% 0.50/0.67  # Paramodulations                      : 14161
% 0.50/0.67  # Factorizations                       : 23
% 0.50/0.67  # Equation resolutions                 : 208
% 0.50/0.67  # Propositional unsat checks           : 0
% 0.50/0.67  #    Propositional check models        : 0
% 0.50/0.67  #    Propositional check unsatisfiable : 0
% 0.50/0.67  #    Propositional clauses             : 0
% 0.50/0.67  #    Propositional clauses after purity: 0
% 0.50/0.67  #    Propositional unsat core size     : 0
% 0.50/0.67  #    Propositional preprocessing time  : 0.000
% 0.50/0.67  #    Propositional encoding time       : 0.000
% 0.50/0.67  #    Propositional solver time         : 0.000
% 0.50/0.67  #    Success case prop preproc time    : 0.000
% 0.50/0.67  #    Success case prop encoding time   : 0.000
% 0.50/0.67  #    Success case prop solver time     : 0.000
% 0.50/0.67  # Current number of processed clauses  : 370
% 0.50/0.67  #    Positive orientable unit clauses  : 8
% 0.50/0.67  #    Positive unorientable unit clauses: 0
% 0.50/0.67  #    Negative unit clauses             : 3
% 0.50/0.67  #    Non-unit-clauses                  : 359
% 0.50/0.67  # Current number of unprocessed clauses: 10974
% 0.50/0.67  # ...number of literals in the above   : 69620
% 0.50/0.67  # Current number of archived formulas  : 0
% 0.50/0.67  # Current number of archived clauses   : 186
% 0.50/0.67  # Clause-clause subsumption calls (NU) : 21429
% 0.50/0.67  # Rec. Clause-clause subsumption calls : 7398
% 0.50/0.67  # Non-unit clause-clause subsumptions  : 893
% 0.50/0.67  # Unit Clause-clause subsumption calls : 210
% 0.50/0.67  # Rewrite failures with RHS unbound    : 0
% 0.50/0.67  # BW rewrite match attempts            : 18
% 0.50/0.67  # BW rewrite match successes           : 15
% 0.50/0.67  # Condensation attempts                : 0
% 0.50/0.67  # Condensation successes               : 0
% 0.50/0.67  # Termbank termtop insertions          : 332539
% 0.50/0.68  
% 0.50/0.68  # -------------------------------------------------
% 0.50/0.68  # User time                : 0.312 s
% 0.50/0.68  # System time              : 0.016 s
% 0.50/0.68  # Total time               : 0.327 s
% 0.50/0.68  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
