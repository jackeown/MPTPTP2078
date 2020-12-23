%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0789+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:11 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 380 expanded)
%              Number of clauses        :   52 ( 184 expanded)
%              Number of leaves         :   11 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  237 (1801 expanded)
%              Number of equality atoms :   36 ( 451 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   22 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t39_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( ( v2_wellord1(X2)
          & r1_tarski(X1,k3_relat_1(X2)) )
       => k3_relat_1(k2_wellord1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_wellord1)).

fof(t20_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),k3_relat_1(X2))
        & r1_tarski(k3_relat_1(k2_wellord1(X2,X1)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
      <=> ( v1_relat_2(X1)
          & v8_relat_2(X1)
          & v4_relat_2(X1)
          & v6_relat_2(X1)
          & v1_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(d6_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(l1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> ! [X2] :
            ( r2_hidden(X2,k3_relat_1(X1))
           => r2_hidden(k4_tarski(X2,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_wellord1)).

fof(t106_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(dt_k2_wellord1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k2_wellord1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(c_0_11,plain,(
    ! [X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X17,X14)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( r2_hidden(X17,X15)
        | ~ r2_hidden(X17,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(X18,X14)
        | ~ r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X16 != k3_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X19,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X19)
        | ~ r2_hidden(esk2_3(X19,X20,X21),X20)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X19)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) )
      & ( r2_hidden(esk2_3(X19,X20,X21),X20)
        | r2_hidden(esk2_3(X19,X20,X21),X21)
        | X21 = k3_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( ( v2_wellord1(X2)
            & r1_tarski(X1,k3_relat_1(X2)) )
         => k3_relat_1(k2_wellord1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t39_wellord1])).

cnf(c_0_15,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X2) ),
    inference(ef,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v2_wellord1(esk5_0)
    & r1_tarski(esk4_0,k3_relat_1(esk5_0))
    & k3_relat_1(k2_wellord1(esk5_0,esk4_0)) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X34,X35] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X35,X34)),k3_relat_1(X35))
        | ~ v1_relat_1(X35) )
      & ( r1_tarski(k3_relat_1(k2_wellord1(X35,X34)),X34)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_wellord1])])])).

cnf(c_0_19,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r2_hidden(esk2_3(X1,X2,X2),X3)
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk4_0,k3_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = X2
    | ~ r2_hidden(esk2_3(X1,X2,X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k3_xboole_0(X1,esk4_0) = esk4_0
    | r2_hidden(esk2_3(X1,esk4_0,esk4_0),k3_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k3_relat_1(k2_wellord1(esk5_0,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k3_xboole_0(k3_relat_1(esk5_0),esk4_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k3_relat_1(k2_wellord1(esk5_0,X1)) = X1
    | ~ r1_tarski(X1,k3_relat_1(k2_wellord1(esk5_0,X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_35,plain,(
    ! [X13] :
      ( ( v1_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v8_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v4_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v6_relat_2(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( v1_wellord1(X13)
        | ~ v2_wellord1(X13)
        | ~ v1_relat_1(X13) )
      & ( ~ v1_relat_2(X13)
        | ~ v8_relat_2(X13)
        | ~ v4_relat_2(X13)
        | ~ v6_relat_2(X13)
        | ~ v1_wellord1(X13)
        | v2_wellord1(X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_wellord1])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk5_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k3_relat_1(k2_wellord1(esk5_0,X1)) = X1
    | r2_hidden(esk1_2(X1,k3_relat_1(k2_wellord1(esk5_0,X1))),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k3_relat_1(k2_wellord1(esk5_0,esk4_0)) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,plain,
    ( k3_xboole_0(X1,X2) = X1
    | r2_hidden(esk2_3(X1,X2,X1),X1) ),
    inference(ef,[status(thm)],[c_0_34])).

fof(c_0_41,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | k2_wellord1(X23,X24) = k3_xboole_0(X23,k2_zfmisc_1(X24,X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_wellord1])])])).

fof(c_0_42,plain,(
    ! [X27,X28] :
      ( ( ~ v1_relat_2(X27)
        | ~ r2_hidden(X28,k3_relat_1(X27))
        | r2_hidden(k4_tarski(X28,X28),X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk3_1(X27),k3_relat_1(X27))
        | v1_relat_2(X27)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X27),esk3_1(X27)),X27)
        | v1_relat_2(X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_wellord1])])])])])).

cnf(c_0_43,plain,
    ( v1_relat_2(X1)
    | ~ v2_wellord1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v2_wellord1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),k3_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_47,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r2_hidden(esk2_3(X1,X2,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_40]),c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk4_0,X1) = esk4_0
    | r2_hidden(esk2_3(esk4_0,X1,esk4_0),k3_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_49,plain,
    ( k2_wellord1(X1,X2) = k3_xboole_0(X1,k2_zfmisc_1(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X2,X2),X1)
    | ~ v1_relat_2(X1)
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_2(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_24])])).

fof(c_0_52,plain,(
    ! [X30,X31,X32,X33] :
      ( ( r2_hidden(X30,X32)
        | ~ r2_hidden(k4_tarski(X30,X31),k2_zfmisc_1(X32,X33)) )
      & ( r2_hidden(X31,X33)
        | ~ r2_hidden(k4_tarski(X30,X31),k2_zfmisc_1(X32,X33)) )
      & ( ~ r2_hidden(X30,X32)
        | ~ r2_hidden(X31,X33)
        | r2_hidden(k4_tarski(X30,X31),k2_zfmisc_1(X32,X33)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_zfmisc_1])])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),k3_xboole_0(X1,k3_relat_1(esk5_0)))
    | ~ r2_hidden(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k3_xboole_0(esk4_0,k3_relat_1(esk5_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_55,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | v1_relat_1(k2_wellord1(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_wellord1])])).

cnf(c_0_56,negated_conjecture,
    ( k3_xboole_0(esk5_0,k2_zfmisc_1(X1,X1)) = k2_wellord1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_24])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),esk5_0)
    | ~ r2_hidden(X1,k3_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_24])])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_38]),c_0_54]),c_0_39])).

fof(c_0_60,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,k3_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(X37,k3_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_61,plain,
    ( v1_relat_1(k2_wellord1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k2_wellord1(esk5_0,X2))
    | ~ r2_hidden(X1,k2_zfmisc_1(X2,X2))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0)))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0)))),k2_zfmisc_1(X2,esk4_0))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(k2_wellord1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_24])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0)))),k2_wellord1(esk5_0,X1))
    | ~ r2_hidden(k4_tarski(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0)))),k2_zfmisc_1(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0)))),k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(k2_wellord1(esk5_0,X2)))
    | ~ r2_hidden(k4_tarski(X3,X1),k2_wellord1(esk5_0,X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0)))),k2_wellord1(esk5_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))),k3_relat_1(k2_wellord1(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk4_0,k3_relat_1(k2_wellord1(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_73]),c_0_29])]),c_0_39]),
    [proof]).

%------------------------------------------------------------------------------
