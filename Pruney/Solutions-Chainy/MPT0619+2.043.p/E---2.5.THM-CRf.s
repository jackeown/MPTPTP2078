%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 252 expanded)
%              Number of clauses        :   38 (  99 expanded)
%              Number of leaves         :   13 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  226 ( 664 expanded)
%              Number of equality atoms :  134 ( 435 expanded)
%              Maximal formula depth    :   32 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_13,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42,X43,X44,X45,X46,X47,X48,X49] :
      ( ( ~ r2_hidden(X42,X41)
        | X42 = X36
        | X42 = X37
        | X42 = X38
        | X42 = X39
        | X42 = X40
        | X41 != k3_enumset1(X36,X37,X38,X39,X40) )
      & ( X43 != X36
        | r2_hidden(X43,X41)
        | X41 != k3_enumset1(X36,X37,X38,X39,X40) )
      & ( X43 != X37
        | r2_hidden(X43,X41)
        | X41 != k3_enumset1(X36,X37,X38,X39,X40) )
      & ( X43 != X38
        | r2_hidden(X43,X41)
        | X41 != k3_enumset1(X36,X37,X38,X39,X40) )
      & ( X43 != X39
        | r2_hidden(X43,X41)
        | X41 != k3_enumset1(X36,X37,X38,X39,X40) )
      & ( X43 != X40
        | r2_hidden(X43,X41)
        | X41 != k3_enumset1(X36,X37,X38,X39,X40) )
      & ( esk3_6(X44,X45,X46,X47,X48,X49) != X44
        | ~ r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk3_6(X44,X45,X46,X47,X48,X49) != X45
        | ~ r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk3_6(X44,X45,X46,X47,X48,X49) != X46
        | ~ r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk3_6(X44,X45,X46,X47,X48,X49) != X47
        | ~ r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk3_6(X44,X45,X46,X47,X48,X49) != X48
        | ~ r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)
        | esk3_6(X44,X45,X46,X47,X48,X49) = X44
        | esk3_6(X44,X45,X46,X47,X48,X49) = X45
        | esk3_6(X44,X45,X46,X47,X48,X49) = X46
        | esk3_6(X44,X45,X46,X47,X48,X49) = X47
        | esk3_6(X44,X45,X46,X47,X48,X49) = X48
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

fof(c_0_14,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_15,plain,(
    ! [X27,X28,X29,X30,X31,X32] : k5_enumset1(X27,X27,X28,X29,X30,X31,X32) = k4_enumset1(X27,X28,X29,X30,X31,X32) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & k1_relat_1(esk8_0) = k1_tarski(esk7_0)
    & k2_relat_1(esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

cnf(c_0_25,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X5,X6,X7,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( X1 = X7
    | X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X4,X5,X6,X7)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_18]),c_0_19])).

fof(c_0_33,plain,(
    ! [X52,X53,X54,X56,X57,X58,X60] :
      ( ( r2_hidden(esk4_3(X52,X53,X54),k1_relat_1(X52))
        | ~ r2_hidden(X54,X53)
        | X53 != k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( X54 = k1_funct_1(X52,esk4_3(X52,X53,X54))
        | ~ r2_hidden(X54,X53)
        | X53 != k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( ~ r2_hidden(X57,k1_relat_1(X52))
        | X56 != k1_funct_1(X52,X57)
        | r2_hidden(X56,X53)
        | X53 != k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( ~ r2_hidden(esk5_2(X52,X58),X58)
        | ~ r2_hidden(X60,k1_relat_1(X52))
        | esk5_2(X52,X58) != k1_funct_1(X52,X60)
        | X58 = k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( r2_hidden(esk6_2(X52,X58),k1_relat_1(X52))
        | r2_hidden(esk5_2(X52,X58),X58)
        | X58 = k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( esk5_2(X52,X58) = k1_funct_1(X52,esk6_2(X52,X58))
        | r2_hidden(esk5_2(X52,X58),X58)
        | X58 = k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_34,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk8_0) = k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_18]),c_0_19])).

cnf(c_0_37,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,k5_enumset1(X6,X6,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_39,plain,(
    ! [X33,X34] :
      ( ( r2_hidden(esk2_2(X33,X34),X33)
        | X33 = k1_tarski(X34)
        | X33 = k1_xboole_0 )
      & ( esk2_2(X33,X34) != X34
        | X33 = k1_tarski(X34)
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_42,plain,(
    ! [X51] :
      ( ( k1_relat_1(X51) != k1_xboole_0
        | k2_relat_1(X51) = k1_xboole_0
        | ~ v1_relat_1(X51) )
      & ( k2_relat_1(X51) != k1_xboole_0
        | k1_relat_1(X51) = k1_xboole_0
        | ~ v1_relat_1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_43,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_45,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_53,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( esk4_3(esk8_0,k2_relat_1(esk8_0),X1) = esk7_0
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_55,negated_conjecture,
    ( k2_relat_1(esk8_0) != k5_enumset1(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_18]),c_0_19])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_18]),c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk8_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_47])])).

cnf(c_0_58,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_0) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_46]),c_0_47])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56])]),c_0_57])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_18]),c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)) = k1_funct_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_55]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.13/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.13/0.38  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.13/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.38  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.13/0.38  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.13/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.38  fof(c_0_13, plain, ![X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X42,X41)|(X42=X36|X42=X37|X42=X38|X42=X39|X42=X40)|X41!=k3_enumset1(X36,X37,X38,X39,X40))&(((((X43!=X36|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40))&(X43!=X37|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40)))&(X43!=X38|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40)))&(X43!=X39|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40)))&(X43!=X40|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40))))&((((((esk3_6(X44,X45,X46,X47,X48,X49)!=X44|~r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48))&(esk3_6(X44,X45,X46,X47,X48,X49)!=X45|~r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48)))&(esk3_6(X44,X45,X46,X47,X48,X49)!=X46|~r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48)))&(esk3_6(X44,X45,X46,X47,X48,X49)!=X47|~r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48)))&(esk3_6(X44,X45,X46,X47,X48,X49)!=X48|~r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48)))&(r2_hidden(esk3_6(X44,X45,X46,X47,X48,X49),X49)|(esk3_6(X44,X45,X46,X47,X48,X49)=X44|esk3_6(X44,X45,X46,X47,X48,X49)=X45|esk3_6(X44,X45,X46,X47,X48,X49)=X46|esk3_6(X44,X45,X46,X47,X48,X49)=X47|esk3_6(X44,X45,X46,X47,X48,X49)=X48)|X49=k3_enumset1(X44,X45,X46,X47,X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  fof(c_0_15, plain, ![X27, X28, X29, X30, X31, X32]:k5_enumset1(X27,X27,X28,X29,X30,X31,X32)=k4_enumset1(X27,X28,X29,X30,X31,X32), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.13/0.38  cnf(c_0_17, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_19, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&(k1_relat_1(esk8_0)=k1_tarski(esk7_0)&k2_relat_1(esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_22, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_23, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_24, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  cnf(c_0_25, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X5,X6,X7,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (k1_relat_1(esk8_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_29, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_30, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_31, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_32, plain, (X1=X7|X1=X6|X1=X5|X1=X4|X1=X3|X2!=k5_enumset1(X3,X3,X3,X4,X5,X6,X7)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_18]), c_0_19])).
% 0.13/0.38  fof(c_0_33, plain, ![X52, X53, X54, X56, X57, X58, X60]:((((r2_hidden(esk4_3(X52,X53,X54),k1_relat_1(X52))|~r2_hidden(X54,X53)|X53!=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(X54=k1_funct_1(X52,esk4_3(X52,X53,X54))|~r2_hidden(X54,X53)|X53!=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(~r2_hidden(X57,k1_relat_1(X52))|X56!=k1_funct_1(X52,X57)|r2_hidden(X56,X53)|X53!=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&((~r2_hidden(esk5_2(X52,X58),X58)|(~r2_hidden(X60,k1_relat_1(X52))|esk5_2(X52,X58)!=k1_funct_1(X52,X60))|X58=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&((r2_hidden(esk6_2(X52,X58),k1_relat_1(X52))|r2_hidden(esk5_2(X52,X58),X58)|X58=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(esk5_2(X52,X58)=k1_funct_1(X52,esk6_2(X52,X58))|r2_hidden(esk5_2(X52,X58),X58)|X58=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.13/0.38  fof(c_0_34, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.38  cnf(c_0_35, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X3,X4,X5,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk8_0)=k5_enumset1(esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_37, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,k5_enumset1(X6,X6,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_38, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  fof(c_0_39, plain, ![X33, X34]:((r2_hidden(esk2_2(X33,X34),X33)|(X33=k1_tarski(X34)|X33=k1_xboole_0))&(esk2_2(X33,X34)!=X34|(X33=k1_tarski(X34)|X33=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.13/0.38  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  fof(c_0_42, plain, ![X51]:((k1_relat_1(X51)!=k1_xboole_0|k2_relat_1(X51)=k1_xboole_0|~v1_relat_1(X51))&(k2_relat_1(X51)!=k1_xboole_0|k1_relat_1(X51)=k1_xboole_0|~v1_relat_1(X51))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.13/0.38  cnf(c_0_43, plain, (X1=k1_funct_1(X2,esk4_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.13/0.38  cnf(c_0_45, plain, (r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_38])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k2_relat_1(esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_49, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (~v1_xboole_0(k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.38  cnf(c_0_51, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.38  cnf(c_0_52, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.38  cnf(c_0_53, plain, (k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (esk4_3(esk8_0,k2_relat_1(esk8_0),X1)=esk7_0|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (k2_relat_1(esk8_0)!=k5_enumset1(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_56, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k2_relat_1(esk8_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_47])])).
% 0.13/0.38  cnf(c_0_58, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk8_0,esk7_0)=X1|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_46]), c_0_47])])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56])]), c_0_57])).
% 0.13/0.38  cnf(c_0_61, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_18]), c_0_19])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (esk2_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))=k1_funct_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_55]), c_0_57]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 64
% 0.13/0.38  # Proof object clause steps            : 38
% 0.13/0.38  # Proof object formula steps           : 26
% 0.13/0.38  # Proof object conjectures             : 18
% 0.13/0.38  # Proof object clause conjectures      : 15
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 19
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 9
% 0.13/0.38  # Proof object simplifying inferences  : 46
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 35
% 0.13/0.38  # Removed in clause preprocessing      : 6
% 0.13/0.38  # Initial clauses in saturation        : 29
% 0.13/0.38  # Processed clauses                    : 161
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 50
% 0.13/0.38  # ...remaining for further processing  : 110
% 0.13/0.38  # Other redundant clauses eliminated   : 42
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 4
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 345
% 0.13/0.38  # ...of the previous two non-trivial   : 245
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 225
% 0.13/0.38  # Factorizations                       : 84
% 0.13/0.38  # Equation resolutions                 : 42
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 65
% 0.13/0.38  #    Positive orientable unit clauses  : 16
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 44
% 0.13/0.38  # Current number of unprocessed clauses: 139
% 0.13/0.38  # ...number of literals in the above   : 700
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 42
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 249
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 126
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 30
% 0.13/0.38  # Unit Clause-clause subsumption calls : 12
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 23
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 5912
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.038 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.043 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
