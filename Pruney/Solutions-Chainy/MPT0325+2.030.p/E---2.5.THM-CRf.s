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
% DateTime   : Thu Dec  3 10:44:09 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 494 expanded)
%              Number of clauses        :   61 ( 236 expanded)
%              Number of leaves         :    8 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          :  230 (1659 expanded)
%              Number of equality atoms :   50 ( 345 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_8,plain,(
    ! [X22,X23,X25,X26,X27] :
      ( ( r1_xboole_0(X22,X23)
        | r2_hidden(esk3_2(X22,X23),k3_xboole_0(X22,X23)) )
      & ( ~ r2_hidden(X27,k3_xboole_0(X25,X26))
        | ~ r1_xboole_0(X25,X26) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_9,plain,(
    ! [X28] :
      ( X28 = k1_xboole_0
      | r2_hidden(esk4_1(X28),X28) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_10,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X30] : r1_xboole_0(X30,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_13,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,plain,(
    ! [X48,X49,X50,X51] :
      ( ( r2_hidden(X48,X50)
        | ~ r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)) )
      & ( r2_hidden(X49,X51)
        | ~ r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)) )
      & ( ~ r2_hidden(X48,X50)
        | ~ r2_hidden(X49,X51)
        | r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X31,X32,X33,X34,X37,X38,X39,X40,X41,X42,X44,X45] :
      ( ( r2_hidden(esk5_4(X31,X32,X33,X34),X31)
        | ~ r2_hidden(X34,X33)
        | X33 != k2_zfmisc_1(X31,X32) )
      & ( r2_hidden(esk6_4(X31,X32,X33,X34),X32)
        | ~ r2_hidden(X34,X33)
        | X33 != k2_zfmisc_1(X31,X32) )
      & ( X34 = k4_tarski(esk5_4(X31,X32,X33,X34),esk6_4(X31,X32,X33,X34))
        | ~ r2_hidden(X34,X33)
        | X33 != k2_zfmisc_1(X31,X32) )
      & ( ~ r2_hidden(X38,X31)
        | ~ r2_hidden(X39,X32)
        | X37 != k4_tarski(X38,X39)
        | r2_hidden(X37,X33)
        | X33 != k2_zfmisc_1(X31,X32) )
      & ( ~ r2_hidden(esk7_3(X40,X41,X42),X42)
        | ~ r2_hidden(X44,X40)
        | ~ r2_hidden(X45,X41)
        | esk7_3(X40,X41,X42) != k4_tarski(X44,X45)
        | X42 = k2_zfmisc_1(X40,X41) )
      & ( r2_hidden(esk8_3(X40,X41,X42),X40)
        | r2_hidden(esk7_3(X40,X41,X42),X42)
        | X42 = k2_zfmisc_1(X40,X41) )
      & ( r2_hidden(esk9_3(X40,X41,X42),X41)
        | r2_hidden(esk7_3(X40,X41,X42),X42)
        | X42 = k2_zfmisc_1(X40,X41) )
      & ( esk7_3(X40,X41,X42) = k4_tarski(esk8_3(X40,X41,X42),esk9_3(X40,X41,X42))
        | r2_hidden(esk7_3(X40,X41,X42),X42)
        | X42 = k2_zfmisc_1(X40,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_19,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0))
    & k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0
    & ( ~ r1_tarski(esk10_0,esk12_0)
      | ~ r1_tarski(esk11_0,esk13_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_23,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | ~ r2_hidden(X1,X5)
    | ~ r1_tarski(k2_zfmisc_1(X5,X4),X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_23]),c_0_17])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk12_0,esk13_0))
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(k2_zfmisc_1(esk10_0,esk11_0),X1),k2_zfmisc_1(esk12_0,esk13_0))
    | r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,esk13_0)
    | ~ r2_hidden(X1,esk11_0)
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X1)
    | r2_hidden(esk7_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_11])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),k3_xboole_0(X1,k2_zfmisc_1(esk12_0,esk13_0)))
    | ~ r2_hidden(esk1_2(k2_zfmisc_1(esk10_0,esk11_0),k3_xboole_0(X1,k2_zfmisc_1(esk12_0,esk13_0))),X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(esk11_0,X1),esk13_0)
    | r1_tarski(esk11_0,X1)
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk7_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_40]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk12_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_35])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_26])).

cnf(c_0_50,negated_conjecture,
    ( k2_zfmisc_1(esk10_0,esk11_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk11_0,X1),esk13_0)
    | r1_tarski(esk11_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r2_hidden(X1,esk12_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(esk6_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_20,c_0_30])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_1(k2_zfmisc_1(esk10_0,esk11_0)),k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk10_0,esk12_0)
    | ~ r1_tarski(esk11_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r1_tarski(esk11_0,esk13_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk10_0,X1),esk12_0)
    | r1_tarski(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_26])).

cnf(c_0_60,plain,
    ( r2_hidden(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
    | ~ r1_tarski(X4,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk4_1(k2_zfmisc_1(esk10_0,esk11_0)),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X1))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_64,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | ~ r1_tarski(esk10_0,esk12_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | r1_tarski(esk10_0,esk12_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_59])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_60])).

cnf(c_0_67,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | r2_hidden(esk4_1(k3_xboole_0(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r1_tarski(esk10_0,k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k3_xboole_0(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | esk10_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_11])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_73,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_xboole_0(esk10_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_70]),c_0_71])])).

cnf(c_0_76,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_29])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75]),c_0_76])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n011.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 20:26:57 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.15/0.31  # Version: 2.5pre002
% 0.15/0.31  # No SInE strategy applied
% 0.15/0.31  # Trying AutoSched0 for 299 seconds
% 0.60/0.78  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.60/0.78  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.60/0.78  #
% 0.60/0.78  # Preprocessing time       : 0.043 s
% 0.60/0.78  # Presaturation interreduction done
% 0.60/0.78  
% 0.60/0.78  # Proof found!
% 0.60/0.78  # SZS status Theorem
% 0.60/0.78  # SZS output start CNFRefutation
% 0.60/0.78  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.60/0.78  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.60/0.78  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.60/0.78  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.60/0.78  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.60/0.78  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.60/0.78  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.60/0.78  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.60/0.78  fof(c_0_8, plain, ![X22, X23, X25, X26, X27]:((r1_xboole_0(X22,X23)|r2_hidden(esk3_2(X22,X23),k3_xboole_0(X22,X23)))&(~r2_hidden(X27,k3_xboole_0(X25,X26))|~r1_xboole_0(X25,X26))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.60/0.78  fof(c_0_9, plain, ![X28]:(X28=k1_xboole_0|r2_hidden(esk4_1(X28),X28)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.60/0.78  cnf(c_0_10, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.78  cnf(c_0_11, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.60/0.78  fof(c_0_12, plain, ![X30]:r1_xboole_0(X30,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.60/0.78  fof(c_0_13, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.60/0.78  fof(c_0_14, plain, ![X48, X49, X50, X51]:(((r2_hidden(X48,X50)|~r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)))&(r2_hidden(X49,X51)|~r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51))))&(~r2_hidden(X48,X50)|~r2_hidden(X49,X51)|r2_hidden(k4_tarski(X48,X49),k2_zfmisc_1(X50,X51)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.60/0.78  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.60/0.78  cnf(c_0_16, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.60/0.78  cnf(c_0_17, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.60/0.78  fof(c_0_18, plain, ![X31, X32, X33, X34, X37, X38, X39, X40, X41, X42, X44, X45]:(((((r2_hidden(esk5_4(X31,X32,X33,X34),X31)|~r2_hidden(X34,X33)|X33!=k2_zfmisc_1(X31,X32))&(r2_hidden(esk6_4(X31,X32,X33,X34),X32)|~r2_hidden(X34,X33)|X33!=k2_zfmisc_1(X31,X32)))&(X34=k4_tarski(esk5_4(X31,X32,X33,X34),esk6_4(X31,X32,X33,X34))|~r2_hidden(X34,X33)|X33!=k2_zfmisc_1(X31,X32)))&(~r2_hidden(X38,X31)|~r2_hidden(X39,X32)|X37!=k4_tarski(X38,X39)|r2_hidden(X37,X33)|X33!=k2_zfmisc_1(X31,X32)))&((~r2_hidden(esk7_3(X40,X41,X42),X42)|(~r2_hidden(X44,X40)|~r2_hidden(X45,X41)|esk7_3(X40,X41,X42)!=k4_tarski(X44,X45))|X42=k2_zfmisc_1(X40,X41))&(((r2_hidden(esk8_3(X40,X41,X42),X40)|r2_hidden(esk7_3(X40,X41,X42),X42)|X42=k2_zfmisc_1(X40,X41))&(r2_hidden(esk9_3(X40,X41,X42),X41)|r2_hidden(esk7_3(X40,X41,X42),X42)|X42=k2_zfmisc_1(X40,X41)))&(esk7_3(X40,X41,X42)=k4_tarski(esk8_3(X40,X41,X42),esk9_3(X40,X41,X42))|r2_hidden(esk7_3(X40,X41,X42),X42)|X42=k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.60/0.78  fof(c_0_19, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.60/0.78  cnf(c_0_20, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.78  fof(c_0_22, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0))&(k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0&(~r1_tarski(esk10_0,esk12_0)|~r1_tarski(esk11_0,esk13_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.60/0.78  cnf(c_0_23, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.60/0.78  cnf(c_0_24, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.78  cnf(c_0_25, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.78  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|~r2_hidden(X1,X5)|~r1_tarski(k2_zfmisc_1(X5,X4),X3)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.60/0.78  cnf(c_0_28, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.78  cnf(c_0_29, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_23]), c_0_17])])).
% 0.60/0.78  cnf(c_0_30, plain, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.60/0.78  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.60/0.78  cnf(c_0_32, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_25])).
% 0.60/0.78  cnf(c_0_33, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_20, c_0_26])).
% 0.60/0.78  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.78  cnf(c_0_35, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk12_0,esk13_0))|~r2_hidden(X2,esk11_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.60/0.78  cnf(c_0_36, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.60/0.78  cnf(c_0_37, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.60/0.78  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(k2_zfmisc_1(esk10_0,esk11_0),X1),k2_zfmisc_1(esk12_0,esk13_0))|r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),X1)), inference(spm,[status(thm)],[c_0_33, c_0_28])).
% 0.60/0.78  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,esk13_0)|~r2_hidden(X1,esk11_0)|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.60/0.78  cnf(c_0_40, plain, (r2_hidden(esk8_3(X1,X2,X3),X1)|r2_hidden(esk7_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.78  cnf(c_0_41, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_36, c_0_11])).
% 0.60/0.78  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.60/0.78  cnf(c_0_43, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),k3_xboole_0(X1,k2_zfmisc_1(esk12_0,esk13_0)))|~r2_hidden(esk1_2(k2_zfmisc_1(esk10_0,esk11_0),k3_xboole_0(X1,k2_zfmisc_1(esk12_0,esk13_0))),X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.60/0.78  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(esk11_0,X1),esk13_0)|r1_tarski(esk11_0,X1)|~r2_hidden(X2,esk10_0)), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 0.60/0.78  cnf(c_0_45, plain, (X1=k1_xboole_0|r2_hidden(esk7_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_40]), c_0_41])).
% 0.60/0.78  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,esk12_0)|~r2_hidden(X2,esk11_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_42, c_0_35])).
% 0.60/0.78  cnf(c_0_47, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.60/0.78  cnf(c_0_48, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_20, c_0_11])).
% 0.60/0.78  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk10_0,esk11_0),k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)))), inference(spm,[status(thm)],[c_0_43, c_0_26])).
% 0.60/0.78  cnf(c_0_50, negated_conjecture, (k2_zfmisc_1(esk10_0,esk11_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.78  cnf(c_0_51, negated_conjecture, (esk10_0=k1_xboole_0|r2_hidden(esk1_2(esk11_0,X1),esk13_0)|r1_tarski(esk11_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.60/0.78  cnf(c_0_52, negated_conjecture, (esk11_0=k1_xboole_0|r2_hidden(X1,esk12_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.60/0.78  cnf(c_0_53, plain, (r2_hidden(esk6_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.60/0.78  cnf(c_0_54, plain, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_20, c_0_30])).
% 0.60/0.78  cnf(c_0_55, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_47])).
% 0.60/0.78  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_1(k2_zfmisc_1(esk10_0,esk11_0)),k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])).
% 0.60/0.78  cnf(c_0_57, negated_conjecture, (~r1_tarski(esk10_0,esk12_0)|~r1_tarski(esk11_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.60/0.78  cnf(c_0_58, negated_conjecture, (esk10_0=k1_xboole_0|r1_tarski(esk11_0,esk13_0)), inference(spm,[status(thm)],[c_0_31, c_0_51])).
% 0.60/0.78  cnf(c_0_59, negated_conjecture, (esk11_0=k1_xboole_0|r2_hidden(esk1_2(esk10_0,X1),esk12_0)|r1_tarski(esk10_0,X1)), inference(spm,[status(thm)],[c_0_52, c_0_26])).
% 0.60/0.78  cnf(c_0_60, plain, (r2_hidden(esk6_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_53])).
% 0.60/0.78  cnf(c_0_61, plain, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k2_zfmisc_1(X4,X5))|~r1_tarski(X4,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_10, c_0_54])).
% 0.60/0.78  cnf(c_0_62, negated_conjecture, (r2_hidden(esk4_1(k2_zfmisc_1(esk10_0,esk11_0)),k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.60/0.78  cnf(c_0_63, plain, (r1_tarski(X1,k3_xboole_0(X2,X1))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X1)),X2)), inference(spm,[status(thm)],[c_0_37, c_0_26])).
% 0.60/0.78  cnf(c_0_64, negated_conjecture, (esk10_0=k1_xboole_0|~r1_tarski(esk10_0,esk12_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.60/0.78  cnf(c_0_65, negated_conjecture, (esk11_0=k1_xboole_0|r1_tarski(esk10_0,esk12_0)), inference(spm,[status(thm)],[c_0_31, c_0_59])).
% 0.60/0.78  cnf(c_0_66, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,k1_xboole_0))), inference(spm,[status(thm)],[c_0_29, c_0_60])).
% 0.60/0.78  cnf(c_0_67, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|r2_hidden(esk4_1(k3_xboole_0(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_55, c_0_11])).
% 0.60/0.78  cnf(c_0_68, negated_conjecture, (~r1_xboole_0(X1,X2)|~r1_tarski(esk10_0,k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.60/0.78  cnf(c_0_69, plain, (r1_tarski(X1,k3_xboole_0(X1,X1))), inference(spm,[status(thm)],[c_0_63, c_0_26])).
% 0.60/0.78  cnf(c_0_70, negated_conjecture, (esk11_0=k1_xboole_0|esk10_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.60/0.78  cnf(c_0_71, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_11])).
% 0.60/0.78  cnf(c_0_72, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk3_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.60/0.78  cnf(c_0_73, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_67])).
% 0.60/0.78  cnf(c_0_74, negated_conjecture, (~r1_xboole_0(esk10_0,esk10_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.60/0.78  cnf(c_0_75, negated_conjecture, (esk10_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_70]), c_0_71])])).
% 0.60/0.78  cnf(c_0_76, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_29])).
% 0.60/0.78  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75]), c_0_76])]), ['proof']).
% 0.60/0.78  # SZS output end CNFRefutation
% 0.60/0.78  # Proof object total steps             : 78
% 0.60/0.78  # Proof object clause steps            : 61
% 0.60/0.78  # Proof object formula steps           : 17
% 0.60/0.78  # Proof object conjectures             : 26
% 0.60/0.78  # Proof object clause conjectures      : 23
% 0.60/0.78  # Proof object formula conjectures     : 3
% 0.60/0.78  # Proof object initial clauses used    : 18
% 0.60/0.78  # Proof object initial formulas used   : 8
% 0.60/0.78  # Proof object generating inferences   : 38
% 0.60/0.78  # Proof object simplifying inferences  : 15
% 0.60/0.78  # Training examples: 0 positive, 0 negative
% 0.60/0.78  # Parsed axioms                        : 8
% 0.60/0.78  # Removed by relevancy pruning/SinE    : 0
% 0.60/0.78  # Initial clauses                      : 27
% 0.60/0.78  # Removed in clause preprocessing      : 0
% 0.60/0.78  # Initial clauses in saturation        : 27
% 0.60/0.78  # Processed clauses                    : 6495
% 0.60/0.78  # ...of these trivial                  : 0
% 0.60/0.78  # ...subsumed                          : 5715
% 0.60/0.78  # ...remaining for further processing  : 780
% 0.60/0.78  # Other redundant clauses eliminated   : 8
% 0.60/0.78  # Clauses deleted for lack of memory   : 0
% 0.60/0.78  # Backward-subsumed                    : 38
% 0.60/0.78  # Backward-rewritten                   : 113
% 0.60/0.78  # Generated clauses                    : 38703
% 0.60/0.78  # ...of the previous two non-trivial   : 33204
% 0.60/0.78  # Contextual simplify-reflections      : 0
% 0.60/0.78  # Paramodulations                      : 38676
% 0.60/0.78  # Factorizations                       : 20
% 0.60/0.78  # Equation resolutions                 : 8
% 0.60/0.78  # Propositional unsat checks           : 0
% 0.60/0.78  #    Propositional check models        : 0
% 0.60/0.78  #    Propositional check unsatisfiable : 0
% 0.60/0.78  #    Propositional clauses             : 0
% 0.60/0.78  #    Propositional clauses after purity: 0
% 0.60/0.78  #    Propositional unsat core size     : 0
% 0.60/0.78  #    Propositional preprocessing time  : 0.000
% 0.60/0.78  #    Propositional encoding time       : 0.000
% 0.60/0.78  #    Propositional solver time         : 0.000
% 0.60/0.78  #    Success case prop preproc time    : 0.000
% 0.60/0.78  #    Success case prop encoding time   : 0.000
% 0.60/0.78  #    Success case prop solver time     : 0.000
% 0.60/0.78  # Current number of processed clauses  : 596
% 0.60/0.78  #    Positive orientable unit clauses  : 19
% 0.60/0.78  #    Positive unorientable unit clauses: 0
% 0.60/0.78  #    Negative unit clauses             : 9
% 0.60/0.78  #    Non-unit-clauses                  : 568
% 0.60/0.78  # Current number of unprocessed clauses: 26530
% 0.60/0.78  # ...number of literals in the above   : 83856
% 0.60/0.78  # Current number of archived formulas  : 0
% 0.60/0.78  # Current number of archived clauses   : 177
% 0.60/0.78  # Clause-clause subsumption calls (NU) : 45315
% 0.60/0.78  # Rec. Clause-clause subsumption calls : 36666
% 0.60/0.78  # Non-unit clause-clause subsumptions  : 931
% 0.60/0.78  # Unit Clause-clause subsumption calls : 1329
% 0.60/0.78  # Rewrite failures with RHS unbound    : 0
% 0.60/0.78  # BW rewrite match attempts            : 46
% 0.60/0.78  # BW rewrite match successes           : 3
% 0.60/0.78  # Condensation attempts                : 0
% 0.60/0.78  # Condensation successes               : 0
% 0.60/0.78  # Termbank termtop insertions          : 516545
% 0.60/0.78  
% 0.60/0.78  # -------------------------------------------------
% 0.60/0.78  # User time                : 0.443 s
% 0.60/0.78  # System time              : 0.024 s
% 0.60/0.78  # Total time               : 0.468 s
% 0.60/0.78  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
