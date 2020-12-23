%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:44:01 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 (1079 expanded)
%              Number of clauses        :   67 ( 544 expanded)
%              Number of leaves         :   12 ( 271 expanded)
%              Depth                    :   18
%              Number of atoms          :  269 (3972 expanded)
%              Number of equality atoms :   86 (1208 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t118_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))
        & r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t134_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | ( X1 = X3
          & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(t117_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( X1 != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))
          | r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) )
        & ~ r1_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X43,X44] :
      ( ( k2_zfmisc_1(X43,X44) != k1_xboole_0
        | X43 = k1_xboole_0
        | X44 = k1_xboole_0 )
      & ( X43 != k1_xboole_0
        | k2_zfmisc_1(X43,X44) = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k2_zfmisc_1(X43,X44) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_13,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_14,plain,(
    ! [X39,X40,X41,X42] :
      ( ( r2_hidden(X39,X41)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) )
      & ( ~ r2_hidden(X39,X41)
        | ~ r2_hidden(X40,X42)
        | r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( r2_hidden(X19,X16)
        | ~ r2_hidden(X19,X18)
        | X18 != k3_xboole_0(X16,X17) )
      & ( r2_hidden(X19,X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k3_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X20,X16)
        | ~ r2_hidden(X20,X17)
        | r2_hidden(X20,X18)
        | X18 != k3_xboole_0(X16,X17) )
      & ( ~ r2_hidden(esk3_3(X21,X22,X23),X23)
        | ~ r2_hidden(esk3_3(X21,X22,X23),X21)
        | ~ r2_hidden(esk3_3(X21,X22,X23),X22)
        | X23 = k3_xboole_0(X21,X22) )
      & ( r2_hidden(esk3_3(X21,X22,X23),X21)
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k3_xboole_0(X21,X22) )
      & ( r2_hidden(esk3_3(X21,X22,X23),X22)
        | r2_hidden(esk3_3(X21,X22,X23),X23)
        | X23 = k3_xboole_0(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_16,plain,(
    ! [X48,X49,X50] :
      ( ( r1_tarski(k2_zfmisc_1(X48,X50),k2_zfmisc_1(X49,X50))
        | ~ r1_tarski(X48,X49) )
      & ( r1_tarski(k2_zfmisc_1(X50,X48),k2_zfmisc_1(X50,X49))
        | ~ r1_tarski(X48,X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X25,X26] :
      ( ( r1_tarski(X25,X26)
        | X25 != X26 )
      & ( r1_tarski(X26,X25)
        | X25 != X26 )
      & ( ~ r1_tarski(X25,X26)
        | ~ r1_tarski(X26,X25)
        | X25 = X26 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X27] : r1_tarski(k1_xboole_0,X27) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_25,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | ~ v1_xboole_0(k2_zfmisc_1(X4,X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_30,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r2_hidden(X32,X31)
        | X32 = X28
        | X32 = X29
        | X32 = X30
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X28
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X29
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( X33 != X30
        | r2_hidden(X33,X31)
        | X31 != k1_enumset1(X28,X29,X30) )
      & ( esk4_4(X34,X35,X36,X37) != X34
        | ~ r2_hidden(esk4_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk4_4(X34,X35,X36,X37) != X35
        | ~ r2_hidden(esk4_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( esk4_4(X34,X35,X36,X37) != X36
        | ~ r2_hidden(esk4_4(X34,X35,X36,X37),X37)
        | X37 = k1_enumset1(X34,X35,X36) )
      & ( r2_hidden(esk4_4(X34,X35,X36,X37),X37)
        | esk4_4(X34,X35,X36,X37) = X34
        | esk4_4(X34,X35,X36,X37) = X35
        | esk4_4(X34,X35,X36,X37) = X36
        | X37 = k1_enumset1(X34,X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_27])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2)
    | v1_xboole_0(k3_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_39,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | r2_hidden(esk2_2(k3_xboole_0(X1,X2),X3),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_34])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k3_xboole_0(X1,k1_xboole_0))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_enumset1(X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

fof(c_0_42,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X3,X4)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | ( X1 = X3
            & X2 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t134_zfmisc_1])).

cnf(c_0_43,plain,
    ( ~ r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_38]),c_0_27])])).

cnf(c_0_44,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_34])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k3_xboole_0(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_47,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk7_0,esk8_0)
    & esk5_0 != k1_xboole_0
    & esk6_0 != k1_xboole_0
    & ( esk5_0 != esk7_0
      | esk6_0 != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X4,X5)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_33])).

cnf(c_0_51,plain,
    ( r1_tarski(k3_xboole_0(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = k2_zfmisc_1(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_44]),c_0_49])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_27])])).

cnf(c_0_59,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_19])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(X2,k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_3(X1,k1_xboole_0,esk6_0),esk8_0)
    | ~ r2_hidden(X2,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_62]),c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_3(X1,k1_xboole_0,esk6_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_62]),c_0_67])).

fof(c_0_72,plain,(
    ! [X45,X46,X47] :
      ( ( ~ r1_tarski(k2_zfmisc_1(X46,X45),k2_zfmisc_1(X47,X45))
        | X45 = k1_xboole_0
        | r1_tarski(X46,X47) )
      & ( ~ r1_tarski(k2_zfmisc_1(X45,X46),k2_zfmisc_1(X45,X47))
        | X45 = k1_xboole_0
        | r1_tarski(X46,X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,esk7_0)
    | ~ r2_hidden(esk2_2(X1,esk7_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(X2,X3)
    | ~ r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(X1,esk8_0),k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r1_tarski(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_53])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_34])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_34])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk8_0,esk6_0)
    | ~ r1_tarski(esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(X1,esk8_0))
    | ~ r1_tarski(esk7_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_53])).

cnf(c_0_81,negated_conjecture,
    ( esk7_0 = esk5_0
    | ~ r1_tarski(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( esk8_0 = esk6_0
    | ~ r1_tarski(esk6_0,esk8_0)
    | ~ r1_tarski(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk6_0,esk8_0)
    | ~ r1_tarski(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_80]),c_0_67])).

cnf(c_0_85,negated_conjecture,
    ( esk5_0 != esk7_0
    | esk6_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_86,negated_conjecture,
    ( esk7_0 = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_87,negated_conjecture,
    ( esk8_0 = esk6_0
    | ~ r1_tarski(esk6_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_77])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk6_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_82])])).

cnf(c_0_89,negated_conjecture,
    ( esk8_0 != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.028 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.42  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.42  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.42  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.19/0.42  fof(t118_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>(r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X3))&r1_tarski(k2_zfmisc_1(X3,X1),k2_zfmisc_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.42  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.19/0.42  fof(t134_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 0.19/0.42  fof(t117_zfmisc_1, axiom, ![X1, X2, X3]:~(((X1!=k1_xboole_0&(r1_tarski(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X3,X1))|r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))))&~(r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 0.19/0.42  fof(c_0_12, plain, ![X43, X44]:((k2_zfmisc_1(X43,X44)!=k1_xboole_0|(X43=k1_xboole_0|X44=k1_xboole_0))&((X43!=k1_xboole_0|k2_zfmisc_1(X43,X44)=k1_xboole_0)&(X44!=k1_xboole_0|k2_zfmisc_1(X43,X44)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.42  fof(c_0_13, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.42  fof(c_0_14, plain, ![X39, X40, X41, X42]:(((r2_hidden(X39,X41)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))&(r2_hidden(X40,X42)|~r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42))))&(~r2_hidden(X39,X41)|~r2_hidden(X40,X42)|r2_hidden(k4_tarski(X39,X40),k2_zfmisc_1(X41,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.42  fof(c_0_15, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:((((r2_hidden(X19,X16)|~r2_hidden(X19,X18)|X18!=k3_xboole_0(X16,X17))&(r2_hidden(X19,X17)|~r2_hidden(X19,X18)|X18!=k3_xboole_0(X16,X17)))&(~r2_hidden(X20,X16)|~r2_hidden(X20,X17)|r2_hidden(X20,X18)|X18!=k3_xboole_0(X16,X17)))&((~r2_hidden(esk3_3(X21,X22,X23),X23)|(~r2_hidden(esk3_3(X21,X22,X23),X21)|~r2_hidden(esk3_3(X21,X22,X23),X22))|X23=k3_xboole_0(X21,X22))&((r2_hidden(esk3_3(X21,X22,X23),X21)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k3_xboole_0(X21,X22))&(r2_hidden(esk3_3(X21,X22,X23),X22)|r2_hidden(esk3_3(X21,X22,X23),X23)|X23=k3_xboole_0(X21,X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.19/0.42  fof(c_0_16, plain, ![X48, X49, X50]:((r1_tarski(k2_zfmisc_1(X48,X50),k2_zfmisc_1(X49,X50))|~r1_tarski(X48,X49))&(r1_tarski(k2_zfmisc_1(X50,X48),k2_zfmisc_1(X50,X49))|~r1_tarski(X48,X49))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_17, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.42  cnf(c_0_18, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_19, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  fof(c_0_21, plain, ![X25, X26]:(((r1_tarski(X25,X26)|X25!=X26)&(r1_tarski(X26,X25)|X25!=X26))&(~r1_tarski(X25,X26)|~r1_tarski(X26,X25)|X25=X26)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  cnf(c_0_22, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X2))|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_23, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_17])).
% 0.19/0.42  fof(c_0_24, plain, ![X27]:r1_tarski(k1_xboole_0,X27), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.42  fof(c_0_25, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|~v1_xboole_0(k2_zfmisc_1(X4,X2))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.42  cnf(c_0_27, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.42  cnf(c_0_28, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_29, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  fof(c_0_30, plain, ![X28, X29, X30, X31, X32, X33, X34, X35, X36, X37]:(((~r2_hidden(X32,X31)|(X32=X28|X32=X29|X32=X30)|X31!=k1_enumset1(X28,X29,X30))&(((X33!=X28|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))&(X33!=X29|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30)))&(X33!=X30|r2_hidden(X33,X31)|X31!=k1_enumset1(X28,X29,X30))))&((((esk4_4(X34,X35,X36,X37)!=X34|~r2_hidden(esk4_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36))&(esk4_4(X34,X35,X36,X37)!=X35|~r2_hidden(esk4_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(esk4_4(X34,X35,X36,X37)!=X36|~r2_hidden(esk4_4(X34,X35,X36,X37),X37)|X37=k1_enumset1(X34,X35,X36)))&(r2_hidden(esk4_4(X34,X35,X36,X37),X37)|(esk4_4(X34,X35,X36,X37)=X34|esk4_4(X34,X35,X36,X37)=X35|esk4_4(X34,X35,X36,X37)=X36)|X37=k1_enumset1(X34,X35,X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.19/0.43  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.43  cnf(c_0_32, plain, (r1_tarski(k2_zfmisc_1(X1,X2),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.43  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.43  cnf(c_0_34, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.43  cnf(c_0_35, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X2,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_23]), c_0_27])])).
% 0.19/0.43  cnf(c_0_36, plain, (r2_hidden(esk1_1(k3_xboole_0(X1,X2)),X2)|v1_xboole_0(k3_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.43  cnf(c_0_37, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.43  cnf(c_0_38, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.19/0.43  cnf(c_0_39, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|r2_hidden(esk2_2(k3_xboole_0(X1,X2),X3),X2)), inference(spm,[status(thm)],[c_0_28, c_0_34])).
% 0.19/0.43  cnf(c_0_40, plain, (v1_xboole_0(k3_xboole_0(X1,k1_xboole_0))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.43  cnf(c_0_41, plain, (r2_hidden(X1,k1_enumset1(X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).
% 0.19/0.43  fof(c_0_42, negated_conjecture, ~(![X1, X2, X3, X4]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X3,X4)=>(X1=k1_xboole_0|X2=k1_xboole_0|(X1=X3&X2=X4)))), inference(assume_negation,[status(cth)],[t134_zfmisc_1])).
% 0.19/0.43  cnf(c_0_43, plain, (~r1_tarski(X1,k1_xboole_0)|~r2_hidden(X2,X3)|~r2_hidden(X4,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_38]), c_0_27])])).
% 0.19/0.43  cnf(c_0_44, plain, (r1_tarski(k3_xboole_0(X1,X2),X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_18, c_0_39])).
% 0.19/0.43  cnf(c_0_45, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_18, c_0_34])).
% 0.19/0.43  cnf(c_0_46, plain, (v1_xboole_0(k3_xboole_0(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.43  fof(c_0_47, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk7_0,esk8_0)&((esk5_0!=k1_xboole_0&esk6_0!=k1_xboole_0)&(esk5_0!=esk7_0|esk6_0!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_42])])])).
% 0.19/0.43  cnf(c_0_48, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.43  cnf(c_0_49, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X4,X5)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.43  cnf(c_0_50, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_33])).
% 0.19/0.43  cnf(c_0_51, plain, (r1_tarski(k3_xboole_0(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.43  cnf(c_0_52, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_53, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=k2_zfmisc_1(esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.43  cnf(c_0_54, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_44]), c_0_49])).
% 0.19/0.43  cnf(c_0_55, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.43  cnf(c_0_56, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.43  cnf(c_0_57, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.43  cnf(c_0_58, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_27])])).
% 0.19/0.43  cnf(c_0_59, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.43  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_56, c_0_53])).
% 0.19/0.43  cnf(c_0_61, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk6_0)|~r2_hidden(X2,esk5_0)), inference(spm,[status(thm)],[c_0_57, c_0_19])).
% 0.19/0.43  cnf(c_0_62, plain, (X1=k1_xboole_0|r2_hidden(esk3_3(X2,k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_55])).
% 0.19/0.43  cnf(c_0_63, negated_conjecture, (esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.43  cnf(c_0_64, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X2,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_60, c_0_19])).
% 0.19/0.43  cnf(c_0_65, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_19, c_0_53])).
% 0.19/0.43  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_3(X1,k1_xboole_0,esk6_0),esk8_0)|~r2_hidden(X2,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 0.19/0.43  cnf(c_0_67, negated_conjecture, (esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.43  cnf(c_0_68, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.43  cnf(c_0_69, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_62]), c_0_63])).
% 0.19/0.43  cnf(c_0_70, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_65])).
% 0.19/0.43  cnf(c_0_71, negated_conjecture, (r2_hidden(esk3_3(X1,k1_xboole_0,esk6_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_62]), c_0_67])).
% 0.19/0.43  fof(c_0_72, plain, ![X45, X46, X47]:((~r1_tarski(k2_zfmisc_1(X46,X45),k2_zfmisc_1(X47,X45))|X45=k1_xboole_0|r1_tarski(X46,X47))&(~r1_tarski(k2_zfmisc_1(X45,X46),k2_zfmisc_1(X45,X47))|X45=k1_xboole_0|r1_tarski(X46,X47))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t117_zfmisc_1])])])])).
% 0.19/0.43  cnf(c_0_73, negated_conjecture, (r1_tarski(X1,esk7_0)|~r2_hidden(esk2_2(X1,esk7_0),esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.43  cnf(c_0_74, negated_conjecture, (r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.43  cnf(c_0_75, plain, (X1=k1_xboole_0|r1_tarski(X2,X3)|~r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.43  cnf(c_0_76, negated_conjecture, (r1_tarski(k2_zfmisc_1(X1,esk8_0),k2_zfmisc_1(esk5_0,esk6_0))|~r1_tarski(X1,esk7_0)), inference(spm,[status(thm)],[c_0_22, c_0_53])).
% 0.19/0.43  cnf(c_0_77, negated_conjecture, (r1_tarski(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_73, c_0_34])).
% 0.19/0.43  cnf(c_0_78, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_74, c_0_34])).
% 0.19/0.43  cnf(c_0_79, negated_conjecture, (r1_tarski(esk8_0,esk6_0)|~r1_tarski(esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_67])).
% 0.19/0.43  cnf(c_0_80, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),k2_zfmisc_1(X1,esk8_0))|~r1_tarski(esk7_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_53])).
% 0.19/0.43  cnf(c_0_81, negated_conjecture, (esk7_0=esk5_0|~r1_tarski(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_77])).
% 0.19/0.43  cnf(c_0_82, negated_conjecture, (r1_tarski(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_78])).
% 0.19/0.43  cnf(c_0_83, negated_conjecture, (esk8_0=esk6_0|~r1_tarski(esk6_0,esk8_0)|~r1_tarski(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_31, c_0_79])).
% 0.19/0.43  cnf(c_0_84, negated_conjecture, (r1_tarski(esk6_0,esk8_0)|~r1_tarski(esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_80]), c_0_67])).
% 0.19/0.43  cnf(c_0_85, negated_conjecture, (esk5_0!=esk7_0|esk6_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.43  cnf(c_0_86, negated_conjecture, (esk7_0=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.19/0.43  cnf(c_0_87, negated_conjecture, (esk8_0=esk6_0|~r1_tarski(esk6_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_77])])).
% 0.19/0.43  cnf(c_0_88, negated_conjecture, (r1_tarski(esk6_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_82])])).
% 0.19/0.43  cnf(c_0_89, negated_conjecture, (esk8_0!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.19/0.43  cnf(c_0_90, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])]), c_0_89]), ['proof']).
% 0.19/0.43  # SZS output end CNFRefutation
% 0.19/0.43  # Proof object total steps             : 91
% 0.19/0.43  # Proof object clause steps            : 67
% 0.19/0.43  # Proof object formula steps           : 24
% 0.19/0.43  # Proof object conjectures             : 32
% 0.19/0.43  # Proof object clause conjectures      : 29
% 0.19/0.43  # Proof object formula conjectures     : 3
% 0.19/0.43  # Proof object initial clauses used    : 21
% 0.19/0.43  # Proof object initial formulas used   : 12
% 0.19/0.43  # Proof object generating inferences   : 38
% 0.19/0.43  # Proof object simplifying inferences  : 30
% 0.19/0.43  # Training examples: 0 positive, 0 negative
% 0.19/0.43  # Parsed axioms                        : 12
% 0.19/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.43  # Initial clauses                      : 38
% 0.19/0.43  # Removed in clause preprocessing      : 0
% 0.19/0.43  # Initial clauses in saturation        : 38
% 0.19/0.43  # Processed clauses                    : 809
% 0.19/0.43  # ...of these trivial                  : 5
% 0.19/0.43  # ...subsumed                          : 473
% 0.19/0.43  # ...remaining for further processing  : 331
% 0.19/0.43  # Other redundant clauses eliminated   : 26
% 0.19/0.43  # Clauses deleted for lack of memory   : 0
% 0.19/0.43  # Backward-subsumed                    : 39
% 0.19/0.43  # Backward-rewritten                   : 110
% 0.19/0.43  # Generated clauses                    : 2434
% 0.19/0.43  # ...of the previous two non-trivial   : 2007
% 0.19/0.43  # Contextual simplify-reflections      : 3
% 0.19/0.43  # Paramodulations                      : 2386
% 0.19/0.43  # Factorizations                       : 20
% 0.19/0.43  # Equation resolutions                 : 26
% 0.19/0.43  # Propositional unsat checks           : 0
% 0.19/0.43  #    Propositional check models        : 0
% 0.19/0.43  #    Propositional check unsatisfiable : 0
% 0.19/0.43  #    Propositional clauses             : 0
% 0.19/0.43  #    Propositional clauses after purity: 0
% 0.19/0.43  #    Propositional unsat core size     : 0
% 0.19/0.43  #    Propositional preprocessing time  : 0.000
% 0.19/0.43  #    Propositional encoding time       : 0.000
% 0.19/0.43  #    Propositional solver time         : 0.000
% 0.19/0.43  #    Success case prop preproc time    : 0.000
% 0.19/0.43  #    Success case prop encoding time   : 0.000
% 0.19/0.43  #    Success case prop solver time     : 0.000
% 0.19/0.43  # Current number of processed clauses  : 129
% 0.19/0.43  #    Positive orientable unit clauses  : 22
% 0.19/0.43  #    Positive unorientable unit clauses: 0
% 0.19/0.43  #    Negative unit clauses             : 13
% 0.19/0.43  #    Non-unit-clauses                  : 94
% 0.19/0.43  # Current number of unprocessed clauses: 1241
% 0.19/0.43  # ...number of literals in the above   : 4564
% 0.19/0.43  # Current number of archived formulas  : 0
% 0.19/0.43  # Current number of archived clauses   : 191
% 0.19/0.43  # Clause-clause subsumption calls (NU) : 7101
% 0.19/0.43  # Rec. Clause-clause subsumption calls : 5147
% 0.19/0.43  # Non-unit clause-clause subsumptions  : 211
% 0.19/0.43  # Unit Clause-clause subsumption calls : 920
% 0.19/0.43  # Rewrite failures with RHS unbound    : 0
% 0.19/0.43  # BW rewrite match attempts            : 24
% 0.19/0.43  # BW rewrite match successes           : 14
% 0.19/0.43  # Condensation attempts                : 0
% 0.19/0.43  # Condensation successes               : 0
% 0.19/0.43  # Termbank termtop insertions          : 31123
% 0.19/0.43  
% 0.19/0.43  # -------------------------------------------------
% 0.19/0.43  # User time                : 0.076 s
% 0.19/0.43  # System time              : 0.007 s
% 0.19/0.43  # Total time               : 0.083 s
% 0.19/0.43  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
