%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:40:04 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   67 (1422 expanded)
%              Number of clauses        :   47 ( 620 expanded)
%              Number of leaves         :   10 ( 400 expanded)
%              Depth                    :   18
%              Number of atoms          :  150 (2665 expanded)
%              Number of equality atoms :   95 (2016 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(t44_zfmisc_1,conjecture,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk3_2(X24,X25),X25)
        | esk3_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk3_2(X24,X25),X25)
        | esk3_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X28,X29] : k1_enumset1(X28,X28,X29) = k2_tarski(X28,X29) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,plain,(
    ! [X30,X31,X32] : k2_enumset1(X30,X30,X31,X32) = k1_enumset1(X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_14,plain,(
    ! [X33,X34,X35,X36] : k3_enumset1(X33,X33,X34,X35,X36) = k2_enumset1(X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
          & X2 != X3
          & X2 != k1_xboole_0
          & X3 != k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t44_zfmisc_1])).

fof(c_0_16,plain,(
    ! [X39,X40] : k3_tarski(k2_tarski(X39,X40)) = k2_xboole_0(X39,X40) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

cnf(c_0_17,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0)
    & esk5_0 != esk6_0
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_23,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
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

cnf(c_0_25,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k1_tarski(esk4_0) = k2_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0) = k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_18]),c_0_19]),c_0_27]),c_0_20]),c_0_20]),c_0_21]),c_0_21])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_27]),c_0_20]),c_0_21])).

fof(c_0_32,plain,(
    ! [X14] :
      ( X14 = k1_xboole_0
      | r2_hidden(esk2_1(X14),X14) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_33,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_37,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 = esk2_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X3 != k3_tarski(k3_enumset1(X2,X2,X2,X2,X4))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_27]),c_0_20]),c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk2_1(esk6_0)
    | ~ r2_hidden(X1,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_42])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( X1 = esk2_1(esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( esk5_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_46,c_0_36])).

cnf(c_0_49,negated_conjecture,
    ( X1 = esk2_1(esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( esk2_1(esk6_0) = esk2_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_39]),c_0_48])).

cnf(c_0_51,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( X1 = esk2_1(esk5_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( esk3_2(X1,X2) = X1
    | X2 = k3_enumset1(X1,X1,X1,X1,X1)
    | r2_hidden(esk3_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_54,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( esk6_0 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk3_2(X1,esk6_0) = esk2_1(esk5_0)
    | esk3_2(X1,esk6_0) = X1 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,plain,
    ( X2 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk3_2(X1,X2) != X1
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_18]),c_0_19]),c_0_20]),c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 = k3_enumset1(esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0))
    | esk3_2(esk2_1(esk5_0),esk6_0) = esk2_1(esk5_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_50]),c_0_40])).

cnf(c_0_59,negated_conjecture,
    ( X1 = esk2_1(esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( esk6_0 = k3_enumset1(esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = k3_enumset1(X1,X1,X1,X1,X1)
    | esk3_2(X1,esk5_0) = esk2_1(esk5_0)
    | esk3_2(X1,esk5_0) = X1 ),
    inference(spm,[status(thm)],[c_0_59,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k3_enumset1(esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk3_2(esk2_1(esk5_0),esk5_0) = esk2_1(esk5_0) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_62])]),c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(esk2_1(esk5_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_64]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_39]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.19/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.19/0.37  fof(t44_zfmisc_1, conjecture, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.19/0.37  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.19/0.37  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.37  fof(d2_xboole_0, axiom, k1_xboole_0=o_0_0_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 0.19/0.37  fof(c_0_10, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|X22=X20|X21!=k1_tarski(X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_tarski(X20)))&((~r2_hidden(esk3_2(X24,X25),X25)|esk3_2(X24,X25)!=X24|X25=k1_tarski(X24))&(r2_hidden(esk3_2(X24,X25),X25)|esk3_2(X24,X25)=X24|X25=k1_tarski(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.37  fof(c_0_11, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.37  fof(c_0_12, plain, ![X28, X29]:k1_enumset1(X28,X28,X29)=k2_tarski(X28,X29), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.37  fof(c_0_13, plain, ![X30, X31, X32]:k2_enumset1(X30,X30,X31,X32)=k1_enumset1(X30,X31,X32), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.19/0.37  fof(c_0_14, plain, ![X33, X34, X35, X36]:k3_enumset1(X33,X33,X34,X35,X36)=k2_enumset1(X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.19/0.37  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t44_zfmisc_1])).
% 0.19/0.37  fof(c_0_16, plain, ![X39, X40]:k3_tarski(k2_tarski(X39,X40))=k2_xboole_0(X39,X40), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.19/0.37  cnf(c_0_17, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  cnf(c_0_19, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.37  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_21, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_22, negated_conjecture, (((k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)&esk5_0!=esk6_0)&esk5_0!=k1_xboole_0)&esk6_0!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.37  cnf(c_0_23, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_24, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(r2_hidden(X8,X5)|r2_hidden(X8,X6))|X7!=k2_xboole_0(X5,X6))&((~r2_hidden(X9,X5)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))&(~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k2_xboole_0(X5,X6))))&(((~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11))&(~r2_hidden(esk1_3(X10,X11,X12),X11)|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_xboole_0(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k2_xboole_0(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.37  cnf(c_0_25, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (k1_tarski(esk4_0)=k2_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_27, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_23, c_0_19])).
% 0.19/0.37  cnf(c_0_28, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_29, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k3_enumset1(esk4_0,esk4_0,esk4_0,esk4_0,esk4_0)=k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_18]), c_0_19]), c_0_27]), c_0_20]), c_0_20]), c_0_21]), c_0_21])).
% 0.19/0.37  cnf(c_0_31, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X4,X4,X4,X4,X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_27]), c_0_20]), c_0_21])).
% 0.19/0.37  fof(c_0_32, plain, ![X14]:(X14=k1_xboole_0|r2_hidden(esk2_1(X14),X14)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.37  cnf(c_0_34, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_31])).
% 0.19/0.37  cnf(c_0_35, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_36, plain, (k1_xboole_0=o_0_0_xboole_0), inference(split_conjunct,[status(thm)],[d2_xboole_0])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.37  cnf(c_0_39, plain, (X1=o_0_0_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (esk6_0!=o_0_0_xboole_0), inference(rw,[status(thm)],[c_0_37, c_0_36])).
% 0.19/0.37  cnf(c_0_41, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (esk4_0=esk2_1(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.19/0.37  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X3!=k3_tarski(k3_enumset1(X2,X2,X2,X2,X4))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_27]), c_0_20]), c_0_21])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (X1=esk2_1(esk6_0)|~r2_hidden(X1,k3_tarski(k3_enumset1(esk5_0,esk5_0,esk5_0,esk5_0,esk6_0)))), inference(rw,[status(thm)],[c_0_33, c_0_42])).
% 0.19/0.37  cnf(c_0_45, plain, (r2_hidden(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_43])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (X1=esk2_1(esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (esk5_0!=o_0_0_xboole_0), inference(rw,[status(thm)],[c_0_46, c_0_36])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (X1=esk2_1(esk6_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_38, c_0_42])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (esk2_1(esk6_0)=esk2_1(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_39]), c_0_48])).
% 0.19/0.37  cnf(c_0_51, plain, (r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (X1=esk2_1(esk5_0)|~r2_hidden(X1,esk6_0)), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.37  cnf(c_0_53, plain, (esk3_2(X1,X2)=X1|X2=k3_enumset1(X1,X1,X1,X1,X1)|r2_hidden(esk3_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.19/0.37  cnf(c_0_54, plain, (X2=k1_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (esk6_0=k3_enumset1(X1,X1,X1,X1,X1)|esk3_2(X1,esk6_0)=esk2_1(esk5_0)|esk3_2(X1,esk6_0)=X1), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.37  cnf(c_0_56, plain, (X2=k3_enumset1(X1,X1,X1,X1,X1)|esk3_2(X1,X2)!=X1|~r2_hidden(esk3_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_18]), c_0_19]), c_0_20]), c_0_21])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (esk6_0=k3_enumset1(esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0))|esk3_2(esk2_1(esk5_0),esk6_0)=esk2_1(esk5_0)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_55])])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_1(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_50]), c_0_40])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (X1=esk2_1(esk5_0)|~r2_hidden(X1,esk5_0)), inference(rw,[status(thm)],[c_0_47, c_0_50])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (esk6_0=k3_enumset1(esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, (esk5_0=k3_enumset1(X1,X1,X1,X1,X1)|esk3_2(X1,esk5_0)=esk2_1(esk5_0)|esk3_2(X1,esk5_0)=X1), inference(spm,[status(thm)],[c_0_59, c_0_53])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (k3_enumset1(esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0),esk2_1(esk5_0))!=esk5_0), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.37  cnf(c_0_64, negated_conjecture, (esk3_2(esk2_1(esk5_0),esk5_0)=esk2_1(esk5_0)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_62])]), c_0_63])).
% 0.19/0.37  cnf(c_0_65, negated_conjecture, (~r2_hidden(esk2_1(esk5_0),esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_64]), c_0_63])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_39]), c_0_48]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 67
% 0.19/0.37  # Proof object clause steps            : 47
% 0.19/0.37  # Proof object formula steps           : 20
% 0.19/0.37  # Proof object conjectures             : 28
% 0.19/0.37  # Proof object clause conjectures      : 25
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 16
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 13
% 0.19/0.37  # Proof object simplifying inferences  : 47
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 14
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 29
% 0.19/0.37  # Removed in clause preprocessing      : 5
% 0.19/0.37  # Initial clauses in saturation        : 24
% 0.19/0.37  # Processed clauses                    : 100
% 0.19/0.37  # ...of these trivial                  : 4
% 0.19/0.37  # ...subsumed                          : 3
% 0.19/0.37  # ...remaining for further processing  : 93
% 0.19/0.37  # Other redundant clauses eliminated   : 17
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 27
% 0.19/0.37  # Generated clauses                    : 181
% 0.19/0.37  # ...of the previous two non-trivial   : 171
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 153
% 0.19/0.37  # Factorizations                       : 12
% 0.19/0.37  # Equation resolutions                 : 17
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 35
% 0.19/0.37  #    Positive orientable unit clauses  : 10
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 4
% 0.19/0.37  #    Non-unit-clauses                  : 21
% 0.19/0.37  # Current number of unprocessed clauses: 96
% 0.19/0.37  # ...number of literals in the above   : 328
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 56
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 119
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 94
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.37  # Unit Clause-clause subsumption calls : 45
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 9
% 0.19/0.37  # BW rewrite match successes           : 5
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 4292
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.033 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.036 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
