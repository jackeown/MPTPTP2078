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
% DateTime   : Thu Dec  3 10:52:52 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   85 (1155 expanded)
%              Number of clauses        :   58 ( 478 expanded)
%              Number of leaves         :   13 ( 295 expanded)
%              Depth                    :   17
%              Number of atoms          :  261 (3036 expanded)
%              Number of equality atoms :  136 (1461 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

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

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_14,plain,(
    ! [X40,X41] :
      ( ( ~ r2_hidden(X40,k1_relat_1(X41))
        | k11_relat_1(X41,X40) != k1_xboole_0
        | ~ v1_relat_1(X41) )
      & ( k11_relat_1(X41,X40) = k1_xboole_0
        | r2_hidden(X40,k1_relat_1(X41))
        | ~ v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & k1_relat_1(esk8_0) = k1_tarski(esk7_0)
    & k2_relat_1(esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_17,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X43)
      | ~ r1_tarski(k1_relat_1(X43),X42)
      | k7_relat_1(X43,X42) = X43 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( k11_relat_1(esk8_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( k11_relat_1(esk8_0,esk1_2(X1,k1_relat_1(esk8_0))) = k1_xboole_0
    | r1_tarski(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | k11_relat_1(X36,X37) = k9_relat_1(X36,k1_tarski(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_25,plain,(
    ! [X23] : k2_tarski(X23,X23) = k1_tarski(X23) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X24,X25] : k1_enumset1(X24,X24,X25) = k2_tarski(X24,X25) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] : k2_enumset1(X26,X26,X27,X28) = k1_enumset1(X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,plain,(
    ! [X29,X30,X31,X32] : k3_enumset1(X29,X29,X30,X31,X32) = k2_enumset1(X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_29,negated_conjecture,
    ( k11_relat_1(esk8_0,esk1_2(k1_relat_1(X1),k1_relat_1(esk8_0))) = k1_xboole_0
    | k7_relat_1(X1,k1_relat_1(esk8_0)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | k2_relat_1(k7_relat_1(X39,X38)) = k9_relat_1(X39,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( k11_relat_1(esk8_0,esk1_2(k1_relat_1(esk8_0),k1_relat_1(esk8_0))) = k1_xboole_0
    | k7_relat_1(esk8_0,k1_relat_1(esk8_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_39,plain,
    ( k7_relat_1(X1,X2) = X1
    | r2_hidden(esk1_2(k1_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_30])).

cnf(c_0_40,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_42,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(X16,X15)
        | X16 = X12
        | X16 = X13
        | X16 = X14
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X12
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X13
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( X17 != X14
        | r2_hidden(X17,X15)
        | X15 != k1_enumset1(X12,X13,X14) )
      & ( esk2_4(X18,X19,X20,X21) != X18
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( esk2_4(X18,X19,X20,X21) != X19
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( esk2_4(X18,X19,X20,X21) != X20
        | ~ r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | X21 = k1_enumset1(X18,X19,X20) )
      & ( r2_hidden(esk2_4(X18,X19,X20,X21),X21)
        | esk2_4(X18,X19,X20,X21) = X18
        | esk2_4(X18,X19,X20,X21) = X19
        | esk2_4(X18,X19,X20,X21) = X20
        | X21 = k1_enumset1(X18,X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_43,plain,(
    ! [X44,X45,X46,X48,X49,X50,X52] :
      ( ( r2_hidden(esk4_3(X44,X45,X46),k1_relat_1(X44))
        | ~ r2_hidden(X46,X45)
        | X45 != k2_relat_1(X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( X46 = k1_funct_1(X44,esk4_3(X44,X45,X46))
        | ~ r2_hidden(X46,X45)
        | X45 != k2_relat_1(X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( ~ r2_hidden(X49,k1_relat_1(X44))
        | X48 != k1_funct_1(X44,X49)
        | r2_hidden(X48,X45)
        | X45 != k2_relat_1(X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( ~ r2_hidden(esk5_2(X44,X50),X50)
        | ~ r2_hidden(X52,k1_relat_1(X44))
        | esk5_2(X44,X50) != k1_funct_1(X44,X52)
        | X50 = k2_relat_1(X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( r2_hidden(esk6_2(X44,X50),k1_relat_1(X44))
        | r2_hidden(esk5_2(X44,X50),X50)
        | X50 = k2_relat_1(X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( esk5_2(X44,X50) = k1_funct_1(X44,esk6_2(X44,X50))
        | r2_hidden(esk5_2(X44,X50),X50)
        | X50 = k2_relat_1(X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_44,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(esk8_0,k1_relat_1(esk8_0)) = esk8_0
    | ~ r2_hidden(esk1_2(k1_relat_1(esk8_0),k1_relat_1(esk8_0)),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_18])])).

cnf(c_0_46,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = esk8_0
    | r2_hidden(esk1_2(k1_relat_1(esk8_0),X1),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( k9_relat_1(esk8_0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk8_0) = k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk8_0,X1)) = k9_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_18])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk8_0,k1_relat_1(esk8_0)) = esk8_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k9_relat_1(esk8_0,k1_relat_1(esk8_0)) = k11_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_34]),c_0_35])).

cnf(c_0_55,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | ~ r2_hidden(X1,X2)
    | X2 != k1_enumset1(X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k11_relat_1(esk8_0,esk7_0) = k2_relat_1(esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

fof(c_0_58,plain,(
    ! [X33,X34] :
      ( ( r2_hidden(esk3_2(X33,X34),X33)
        | X33 = k1_tarski(X34)
        | X33 = k1_xboole_0 )
      & ( esk3_2(X33,X34) != X34
        | X33 = k1_tarski(X34)
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).

cnf(c_0_60,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_61,plain,
    ( X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X4,X5)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_34]),c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk4_3(k7_relat_1(esk8_0,X1),k9_relat_1(esk8_0,X1),X2),k1_relat_1(k7_relat_1(esk8_0,X1)))
    | ~ v1_funct_1(k7_relat_1(esk8_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk8_0,X1))
    | ~ r2_hidden(X2,k9_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( k9_relat_1(esk8_0,k1_relat_1(esk8_0)) = k2_relat_1(esk8_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_48])).

cnf(c_0_67,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),X1),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_52]),c_0_52]),c_0_52]),c_0_64]),c_0_52]),c_0_18])])).

cnf(c_0_70,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_71,negated_conjecture,
    ( k2_relat_1(esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_57]),c_0_18]),c_0_66])])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(k7_relat_1(esk8_0,X1),esk4_3(k7_relat_1(esk8_0,X1),k9_relat_1(esk8_0,X1),X2)) = X2
    | ~ v1_funct_1(k7_relat_1(esk8_0,X1))
    | ~ v1_relat_1(k7_relat_1(esk8_0,X1))
    | ~ r2_hidden(X2,k9_relat_1(esk8_0,X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( k2_relat_1(esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_74,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_48])).

cnf(c_0_75,negated_conjecture,
    ( k3_enumset1(X1,X1,X1,X1,X1) = k2_relat_1(esk8_0)
    | r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)),k1_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_63]),c_0_52]),c_0_52]),c_0_52]),c_0_64]),c_0_52]),c_0_18])])).

cnf(c_0_77,negated_conjecture,
    ( k2_relat_1(esk8_0) != k3_enumset1(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_78,negated_conjecture,
    ( esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)) = esk7_0
    | k3_enumset1(X1,X1,X1,X1,X1) = k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk3_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1))) = esk3_2(k2_relat_1(esk8_0),X1)
    | k3_enumset1(X1,X1,X1,X1,X1) = k2_relat_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_70]),c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | esk3_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_32]),c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_83,negated_conjecture,
    ( esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)) = k1_funct_1(esk8_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_80]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_77]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.55/0.72  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.55/0.72  # and selection function SelectCQArNTNpEqFirst.
% 0.55/0.72  #
% 0.55/0.72  # Preprocessing time       : 0.029 s
% 0.55/0.72  # Presaturation interreduction done
% 0.55/0.72  
% 0.55/0.72  # Proof found!
% 0.55/0.72  # SZS status Theorem
% 0.55/0.72  # SZS output start CNFRefutation
% 0.55/0.72  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.55/0.72  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.55/0.72  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.55/0.72  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.55/0.72  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.55/0.72  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.55/0.72  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.55/0.72  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.55/0.72  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.55/0.72  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.55/0.72  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.55/0.72  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.55/0.72  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.55/0.72  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.55/0.72  fof(c_0_14, plain, ![X40, X41]:((~r2_hidden(X40,k1_relat_1(X41))|k11_relat_1(X41,X40)!=k1_xboole_0|~v1_relat_1(X41))&(k11_relat_1(X41,X40)=k1_xboole_0|r2_hidden(X40,k1_relat_1(X41))|~v1_relat_1(X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.55/0.72  fof(c_0_15, negated_conjecture, ((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&(k1_relat_1(esk8_0)=k1_tarski(esk7_0)&k2_relat_1(esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.55/0.72  fof(c_0_16, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.55/0.72  cnf(c_0_17, plain, (k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(X2,k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.72  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.55/0.72  fof(c_0_19, plain, ![X42, X43]:(~v1_relat_1(X43)|(~r1_tarski(k1_relat_1(X43),X42)|k7_relat_1(X43,X42)=X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.55/0.72  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.55/0.72  cnf(c_0_21, negated_conjecture, (k11_relat_1(esk8_0,X1)=k1_xboole_0|r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.55/0.72  cnf(c_0_22, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.55/0.72  cnf(c_0_23, negated_conjecture, (k11_relat_1(esk8_0,esk1_2(X1,k1_relat_1(esk8_0)))=k1_xboole_0|r1_tarski(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.55/0.72  fof(c_0_24, plain, ![X36, X37]:(~v1_relat_1(X36)|k11_relat_1(X36,X37)=k9_relat_1(X36,k1_tarski(X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.55/0.72  fof(c_0_25, plain, ![X23]:k2_tarski(X23,X23)=k1_tarski(X23), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.55/0.72  fof(c_0_26, plain, ![X24, X25]:k1_enumset1(X24,X24,X25)=k2_tarski(X24,X25), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.55/0.72  fof(c_0_27, plain, ![X26, X27, X28]:k2_enumset1(X26,X26,X27,X28)=k1_enumset1(X26,X27,X28), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.55/0.72  fof(c_0_28, plain, ![X29, X30, X31, X32]:k3_enumset1(X29,X29,X30,X31,X32)=k2_enumset1(X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.55/0.72  cnf(c_0_29, negated_conjecture, (k11_relat_1(esk8_0,esk1_2(k1_relat_1(X1),k1_relat_1(esk8_0)))=k1_xboole_0|k7_relat_1(X1,k1_relat_1(esk8_0))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.55/0.72  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.55/0.72  cnf(c_0_31, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.55/0.72  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.55/0.72  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.55/0.72  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.55/0.72  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.55/0.72  fof(c_0_36, plain, ![X38, X39]:(~v1_relat_1(X39)|k2_relat_1(k7_relat_1(X39,X38))=k9_relat_1(X39,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.55/0.72  cnf(c_0_37, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.72  cnf(c_0_38, negated_conjecture, (k11_relat_1(esk8_0,esk1_2(k1_relat_1(esk8_0),k1_relat_1(esk8_0)))=k1_xboole_0|k7_relat_1(esk8_0,k1_relat_1(esk8_0))=esk8_0), inference(spm,[status(thm)],[c_0_29, c_0_18])).
% 0.55/0.72  cnf(c_0_39, plain, (k7_relat_1(X1,X2)=X1|r2_hidden(esk1_2(k1_relat_1(X1),X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_30])).
% 0.55/0.72  cnf(c_0_40, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.55/0.72  cnf(c_0_41, negated_conjecture, (k1_relat_1(esk8_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.55/0.72  fof(c_0_42, plain, ![X12, X13, X14, X15, X16, X17, X18, X19, X20, X21]:(((~r2_hidden(X16,X15)|(X16=X12|X16=X13|X16=X14)|X15!=k1_enumset1(X12,X13,X14))&(((X17!=X12|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14))&(X17!=X13|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14)))&(X17!=X14|r2_hidden(X17,X15)|X15!=k1_enumset1(X12,X13,X14))))&((((esk2_4(X18,X19,X20,X21)!=X18|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20))&(esk2_4(X18,X19,X20,X21)!=X19|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20)))&(esk2_4(X18,X19,X20,X21)!=X20|~r2_hidden(esk2_4(X18,X19,X20,X21),X21)|X21=k1_enumset1(X18,X19,X20)))&(r2_hidden(esk2_4(X18,X19,X20,X21),X21)|(esk2_4(X18,X19,X20,X21)=X18|esk2_4(X18,X19,X20,X21)=X19|esk2_4(X18,X19,X20,X21)=X20)|X21=k1_enumset1(X18,X19,X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.55/0.72  fof(c_0_43, plain, ![X44, X45, X46, X48, X49, X50, X52]:((((r2_hidden(esk4_3(X44,X45,X46),k1_relat_1(X44))|~r2_hidden(X46,X45)|X45!=k2_relat_1(X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(X46=k1_funct_1(X44,esk4_3(X44,X45,X46))|~r2_hidden(X46,X45)|X45!=k2_relat_1(X44)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(~r2_hidden(X49,k1_relat_1(X44))|X48!=k1_funct_1(X44,X49)|r2_hidden(X48,X45)|X45!=k2_relat_1(X44)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&((~r2_hidden(esk5_2(X44,X50),X50)|(~r2_hidden(X52,k1_relat_1(X44))|esk5_2(X44,X50)!=k1_funct_1(X44,X52))|X50=k2_relat_1(X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&((r2_hidden(esk6_2(X44,X50),k1_relat_1(X44))|r2_hidden(esk5_2(X44,X50),X50)|X50=k2_relat_1(X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(esk5_2(X44,X50)=k1_funct_1(X44,esk6_2(X44,X50))|r2_hidden(esk5_2(X44,X50),X50)|X50=k2_relat_1(X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.55/0.72  cnf(c_0_44, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.55/0.72  cnf(c_0_45, negated_conjecture, (k7_relat_1(esk8_0,k1_relat_1(esk8_0))=esk8_0|~r2_hidden(esk1_2(k1_relat_1(esk8_0),k1_relat_1(esk8_0)),k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_18])])).
% 0.55/0.72  cnf(c_0_46, negated_conjecture, (k7_relat_1(esk8_0,X1)=esk8_0|r2_hidden(esk1_2(k1_relat_1(esk8_0),X1),k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_39, c_0_18])).
% 0.55/0.72  cnf(c_0_47, negated_conjecture, (k9_relat_1(esk8_0,k3_enumset1(X1,X1,X1,X1,X1))=k11_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_18])).
% 0.55/0.72  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk8_0)=k3_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.55/0.72  cnf(c_0_49, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.55/0.72  cnf(c_0_50, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.55/0.72  cnf(c_0_51, negated_conjecture, (k2_relat_1(k7_relat_1(esk8_0,X1))=k9_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_44, c_0_18])).
% 0.55/0.72  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk8_0,k1_relat_1(esk8_0))=esk8_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.55/0.72  cnf(c_0_53, negated_conjecture, (k9_relat_1(esk8_0,k1_relat_1(esk8_0))=k11_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.55/0.72  cnf(c_0_54, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X4,X4,X5,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_34]), c_0_35])).
% 0.55/0.72  cnf(c_0_55, plain, (X1=X3|X1=X4|X1=X5|~r2_hidden(X1,X2)|X2!=k1_enumset1(X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.55/0.72  cnf(c_0_56, plain, (r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_50])).
% 0.55/0.72  cnf(c_0_57, negated_conjecture, (k11_relat_1(esk8_0,esk7_0)=k2_relat_1(esk8_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.55/0.72  fof(c_0_58, plain, ![X33, X34]:((r2_hidden(esk3_2(X33,X34),X33)|(X33=k1_tarski(X34)|X33=k1_xboole_0))&(esk3_2(X33,X34)!=X34|(X33=k1_tarski(X34)|X33=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.55/0.72  cnf(c_0_59, plain, (r2_hidden(X1,k3_enumset1(X2,X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_54])])).
% 0.55/0.72  cnf(c_0_60, plain, (X1=k1_funct_1(X2,esk4_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.55/0.72  cnf(c_0_61, plain, (X1=X5|X1=X4|X1=X3|X2!=k3_enumset1(X3,X3,X3,X4,X5)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_34]), c_0_35])).
% 0.55/0.72  cnf(c_0_62, negated_conjecture, (r2_hidden(esk4_3(k7_relat_1(esk8_0,X1),k9_relat_1(esk8_0,X1),X2),k1_relat_1(k7_relat_1(esk8_0,X1)))|~v1_funct_1(k7_relat_1(esk8_0,X1))|~v1_relat_1(k7_relat_1(esk8_0,X1))|~r2_hidden(X2,k9_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_56, c_0_51])).
% 0.55/0.72  cnf(c_0_63, negated_conjecture, (k9_relat_1(esk8_0,k1_relat_1(esk8_0))=k2_relat_1(esk8_0)), inference(rw,[status(thm)],[c_0_53, c_0_57])).
% 0.55/0.72  cnf(c_0_64, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.55/0.72  cnf(c_0_65, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.55/0.72  cnf(c_0_66, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_59, c_0_48])).
% 0.55/0.72  cnf(c_0_67, plain, (k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_60])).
% 0.55/0.72  cnf(c_0_68, plain, (X1=X2|X1=X3|X1=X4|~r2_hidden(X1,k3_enumset1(X4,X4,X4,X3,X2))), inference(er,[status(thm)],[c_0_61])).
% 0.55/0.72  cnf(c_0_69, negated_conjecture, (r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),X1),k1_relat_1(esk8_0))|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_52]), c_0_52]), c_0_52]), c_0_64]), c_0_52]), c_0_18])])).
% 0.55/0.72  cnf(c_0_70, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|r2_hidden(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.55/0.72  cnf(c_0_71, negated_conjecture, (k2_relat_1(esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_57]), c_0_18]), c_0_66])])).
% 0.55/0.72  cnf(c_0_72, negated_conjecture, (k1_funct_1(k7_relat_1(esk8_0,X1),esk4_3(k7_relat_1(esk8_0,X1),k9_relat_1(esk8_0,X1),X2))=X2|~v1_funct_1(k7_relat_1(esk8_0,X1))|~v1_relat_1(k7_relat_1(esk8_0,X1))|~r2_hidden(X2,k9_relat_1(esk8_0,X1))), inference(spm,[status(thm)],[c_0_67, c_0_51])).
% 0.55/0.72  cnf(c_0_73, negated_conjecture, (k2_relat_1(esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.55/0.72  cnf(c_0_74, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_68, c_0_48])).
% 0.55/0.72  cnf(c_0_75, negated_conjecture, (k3_enumset1(X1,X1,X1,X1,X1)=k2_relat_1(esk8_0)|r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)),k1_relat_1(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])).
% 0.55/0.72  cnf(c_0_76, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_63]), c_0_52]), c_0_52]), c_0_52]), c_0_64]), c_0_52]), c_0_18])])).
% 0.55/0.72  cnf(c_0_77, negated_conjecture, (k2_relat_1(esk8_0)!=k3_enumset1(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.55/0.72  cnf(c_0_78, negated_conjecture, (esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1))=esk7_0|k3_enumset1(X1,X1,X1,X1,X1)=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.55/0.72  cnf(c_0_79, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk3_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.55/0.72  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)))=esk3_2(k2_relat_1(esk8_0),X1)|k3_enumset1(X1,X1,X1,X1,X1)=k2_relat_1(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_70]), c_0_71])).
% 0.55/0.72  cnf(c_0_81, negated_conjecture, (esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)))=esk7_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.55/0.72  cnf(c_0_82, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|esk3_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_32]), c_0_33]), c_0_34]), c_0_35])).
% 0.55/0.72  cnf(c_0_83, negated_conjecture, (esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))=k1_funct_1(esk8_0,esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_80]), c_0_81])).
% 0.55/0.72  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_77]), c_0_71]), ['proof']).
% 0.55/0.72  # SZS output end CNFRefutation
% 0.55/0.72  # Proof object total steps             : 85
% 0.55/0.72  # Proof object clause steps            : 58
% 0.55/0.72  # Proof object formula steps           : 27
% 0.55/0.72  # Proof object conjectures             : 34
% 0.55/0.72  # Proof object clause conjectures      : 31
% 0.55/0.72  # Proof object formula conjectures     : 3
% 0.55/0.72  # Proof object initial clauses used    : 21
% 0.55/0.72  # Proof object initial formulas used   : 13
% 0.55/0.72  # Proof object generating inferences   : 25
% 0.55/0.72  # Proof object simplifying inferences  : 55
% 0.55/0.72  # Training examples: 0 positive, 0 negative
% 0.55/0.72  # Parsed axioms                        : 13
% 0.55/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.55/0.72  # Initial clauses                      : 32
% 0.55/0.72  # Removed in clause preprocessing      : 4
% 0.55/0.72  # Initial clauses in saturation        : 28
% 0.55/0.72  # Processed clauses                    : 1272
% 0.55/0.72  # ...of these trivial                  : 2
% 0.55/0.72  # ...subsumed                          : 627
% 0.55/0.72  # ...remaining for further processing  : 643
% 0.55/0.72  # Other redundant clauses eliminated   : 385
% 0.55/0.72  # Clauses deleted for lack of memory   : 0
% 0.55/0.72  # Backward-subsumed                    : 35
% 0.55/0.72  # Backward-rewritten                   : 6
% 0.55/0.72  # Generated clauses                    : 19663
% 0.55/0.72  # ...of the previous two non-trivial   : 17094
% 0.55/0.72  # Contextual simplify-reflections      : 13
% 0.55/0.72  # Paramodulations                      : 19218
% 0.55/0.72  # Factorizations                       : 64
% 0.55/0.72  # Equation resolutions                 : 385
% 0.55/0.72  # Propositional unsat checks           : 0
% 0.55/0.72  #    Propositional check models        : 0
% 0.55/0.72  #    Propositional check unsatisfiable : 0
% 0.55/0.72  #    Propositional clauses             : 0
% 0.55/0.72  #    Propositional clauses after purity: 0
% 0.55/0.72  #    Propositional unsat core size     : 0
% 0.55/0.72  #    Propositional preprocessing time  : 0.000
% 0.55/0.72  #    Propositional encoding time       : 0.000
% 0.55/0.72  #    Propositional solver time         : 0.000
% 0.55/0.72  #    Success case prop preproc time    : 0.000
% 0.55/0.72  #    Success case prop encoding time   : 0.000
% 0.55/0.72  #    Success case prop solver time     : 0.000
% 0.55/0.72  # Current number of processed clauses  : 567
% 0.55/0.72  #    Positive orientable unit clauses  : 15
% 0.55/0.72  #    Positive unorientable unit clauses: 0
% 0.55/0.72  #    Negative unit clauses             : 2
% 0.55/0.72  #    Non-unit-clauses                  : 550
% 0.55/0.72  # Current number of unprocessed clauses: 15780
% 0.55/0.72  # ...number of literals in the above   : 84709
% 0.55/0.72  # Current number of archived formulas  : 0
% 0.55/0.72  # Current number of archived clauses   : 73
% 0.55/0.72  # Clause-clause subsumption calls (NU) : 52555
% 0.55/0.72  # Rec. Clause-clause subsumption calls : 12174
% 0.55/0.72  # Non-unit clause-clause subsumptions  : 675
% 0.55/0.72  # Unit Clause-clause subsumption calls : 281
% 0.55/0.72  # Rewrite failures with RHS unbound    : 0
% 0.55/0.72  # BW rewrite match attempts            : 20
% 0.55/0.72  # BW rewrite match successes           : 4
% 0.55/0.72  # Condensation attempts                : 0
% 0.55/0.72  # Condensation successes               : 0
% 0.55/0.72  # Termbank termtop insertions          : 442682
% 0.55/0.72  
% 0.55/0.72  # -------------------------------------------------
% 0.55/0.72  # User time                : 0.368 s
% 0.55/0.72  # System time              : 0.012 s
% 0.55/0.72  # Total time               : 0.380 s
% 0.55/0.72  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
