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
% DateTime   : Thu Dec  3 10:52:56 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 349 expanded)
%              Number of clauses        :   48 ( 139 expanded)
%              Number of leaves         :   12 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  250 ( 968 expanded)
%              Number of equality atoms :  154 ( 580 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(c_0_12,plain,(
    ! [X52,X53,X54,X56,X57,X58,X60] :
      ( ( r2_hidden(esk3_3(X52,X53,X54),k1_relat_1(X52))
        | ~ r2_hidden(X54,X53)
        | X53 != k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( X54 = k1_funct_1(X52,esk3_3(X52,X53,X54))
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
      & ( ~ r2_hidden(esk4_2(X52,X58),X58)
        | ~ r2_hidden(X60,k1_relat_1(X52))
        | esk4_2(X52,X58) != k1_funct_1(X52,X60)
        | X58 = k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( r2_hidden(esk5_2(X52,X58),k1_relat_1(X52))
        | r2_hidden(esk4_2(X52,X58),X58)
        | X58 = k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( esk4_2(X52,X58) = k1_funct_1(X52,esk5_2(X52,X58))
        | r2_hidden(esk4_2(X52,X58),X58)
        | X58 = k2_relat_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & k1_relat_1(esk7_0) = k1_tarski(esk6_0)
    & k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X33,X34] :
      ( ( r2_hidden(esk1_2(X33,X34),X33)
        | X33 = k1_tarski(X34)
        | X33 = k1_xboole_0 )
      & ( esk1_2(X33,X34) != X34
        | X33 = k1_tarski(X34)
        | X33 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

fof(c_0_17,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X9,X10] : k1_enumset1(X9,X9,X10) = k2_tarski(X9,X10) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X11,X12,X13] : k2_enumset1(X11,X11,X12,X13) = k1_enumset1(X11,X12,X13) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X14,X15,X16,X17] : k3_enumset1(X14,X14,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X18,X19,X20,X21,X22] : k4_enumset1(X18,X18,X19,X20,X21,X22) = k3_enumset1(X18,X19,X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X23,X24,X25,X26,X27,X28] : k5_enumset1(X23,X23,X24,X25,X26,X27,X28) = k4_enumset1(X23,X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

cnf(c_0_23,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
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
      & ( esk2_6(X44,X45,X46,X47,X48,X49) != X44
        | ~ r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk2_6(X44,X45,X46,X47,X48,X49) != X45
        | ~ r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk2_6(X44,X45,X46,X47,X48,X49) != X46
        | ~ r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk2_6(X44,X45,X46,X47,X48,X49) != X47
        | ~ r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( esk2_6(X44,X45,X46,X47,X48,X49) != X48
        | ~ r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) )
      & ( r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)
        | esk2_6(X44,X45,X46,X47,X48,X49) = X44
        | esk2_6(X44,X45,X46,X47,X48,X49) = X45
        | esk2_6(X44,X45,X46,X47,X48,X49) = X46
        | esk2_6(X44,X45,X46,X47,X48,X49) = X47
        | esk2_6(X44,X45,X46,X47,X48,X49) = X48
        | X49 = k3_enumset1(X44,X45,X46,X47,X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk7_0) != k1_tarski(k1_funct_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_27])])).

cnf(c_0_42,plain,
    ( X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | X1 = X7
    | ~ r2_hidden(X1,X2)
    | X2 != k3_enumset1(X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_27])])).

cnf(c_0_44,negated_conjecture,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(esk7_0)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(esk7_0) != k5_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1))) = esk1_2(k2_relat_1(esk7_0),X1)
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(esk7_0)
    | k2_relat_1(esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_47,plain,
    ( X1 = X7
    | X1 = X6
    | X1 = X5
    | X1 = X4
    | X1 = X3
    | X2 != k5_enumset1(X3,X3,X3,X4,X5,X6,X7)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_33]),c_0_34])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_tarski(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,negated_conjecture,
    ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k2_relat_1(esk7_0)
    | k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1))),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)))) = esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))
    | k2_relat_1(esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( X1 = X2
    | X1 = X3
    | X1 = X4
    | X1 = X5
    | X1 = X6
    | ~ r2_hidden(X1,k5_enumset1(X6,X6,X6,X5,X4,X3,X2)) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk7_0) = k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)),k2_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_45])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k5_enumset1(X4,X4,X4,X5,X6,X7,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_33]),c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0
    | r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_54])).

fof(c_0_58,plain,(
    ! [X29,X30] :
      ( ( k2_zfmisc_1(X29,X30) != k1_xboole_0
        | X29 = k1_xboole_0
        | X30 = k1_xboole_0 )
      & ( X29 != k1_xboole_0
        | k2_zfmisc_1(X29,X30) = k1_xboole_0 )
      & ( X30 != k1_xboole_0
        | k2_zfmisc_1(X29,X30) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k5_enumset1(X2,X2,X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).

cnf(c_0_60,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk1_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))) = esk6_0
    | k2_relat_1(esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_62,plain,(
    ! [X31,X32] : ~ r2_hidden(X31,k2_zfmisc_1(X31,X32)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_53])).

cnf(c_0_65,plain,
    ( X1 = k1_xboole_0
    | X1 = k5_enumset1(X2,X2,X2,X2,X2,X2,X2)
    | esk1_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_66,negated_conjecture,
    ( esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)) = k1_funct_1(esk7_0,esk6_0)
    | k2_relat_1(esk7_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_61])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_45])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:02:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.49  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.18/0.49  # and selection function SelectNegativeLiterals.
% 0.18/0.49  #
% 0.18/0.49  # Preprocessing time       : 0.028 s
% 0.18/0.49  # Presaturation interreduction done
% 0.18/0.49  
% 0.18/0.49  # Proof found!
% 0.18/0.49  # SZS status Theorem
% 0.18/0.49  # SZS output start CNFRefutation
% 0.18/0.49  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.18/0.49  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.18/0.49  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.18/0.49  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.49  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.49  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.49  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.49  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.49  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.18/0.49  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 0.18/0.49  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.49  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.18/0.49  fof(c_0_12, plain, ![X52, X53, X54, X56, X57, X58, X60]:((((r2_hidden(esk3_3(X52,X53,X54),k1_relat_1(X52))|~r2_hidden(X54,X53)|X53!=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(X54=k1_funct_1(X52,esk3_3(X52,X53,X54))|~r2_hidden(X54,X53)|X53!=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(~r2_hidden(X57,k1_relat_1(X52))|X56!=k1_funct_1(X52,X57)|r2_hidden(X56,X53)|X53!=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52))))&((~r2_hidden(esk4_2(X52,X58),X58)|(~r2_hidden(X60,k1_relat_1(X52))|esk4_2(X52,X58)!=k1_funct_1(X52,X60))|X58=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&((r2_hidden(esk5_2(X52,X58),k1_relat_1(X52))|r2_hidden(esk4_2(X52,X58),X58)|X58=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(esk4_2(X52,X58)=k1_funct_1(X52,esk5_2(X52,X58))|r2_hidden(esk4_2(X52,X58),X58)|X58=k2_relat_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.18/0.49  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.18/0.49  cnf(c_0_14, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.49  fof(c_0_15, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&(k1_relat_1(esk7_0)=k1_tarski(esk6_0)&k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.18/0.49  fof(c_0_16, plain, ![X33, X34]:((r2_hidden(esk1_2(X33,X34),X33)|(X33=k1_tarski(X34)|X33=k1_xboole_0))&(esk1_2(X33,X34)!=X34|(X33=k1_tarski(X34)|X33=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.18/0.49  fof(c_0_17, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.49  fof(c_0_18, plain, ![X9, X10]:k1_enumset1(X9,X9,X10)=k2_tarski(X9,X10), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.49  fof(c_0_19, plain, ![X11, X12, X13]:k2_enumset1(X11,X11,X12,X13)=k1_enumset1(X11,X12,X13), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.49  fof(c_0_20, plain, ![X14, X15, X16, X17]:k3_enumset1(X14,X14,X15,X16,X17)=k2_enumset1(X14,X15,X16,X17), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.49  fof(c_0_21, plain, ![X18, X19, X20, X21, X22]:k4_enumset1(X18,X18,X19,X20,X21,X22)=k3_enumset1(X18,X19,X20,X21,X22), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.49  fof(c_0_22, plain, ![X23, X24, X25, X26, X27, X28]:k5_enumset1(X23,X23,X24,X25,X26,X27,X28)=k4_enumset1(X23,X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.18/0.49  cnf(c_0_23, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.49  cnf(c_0_24, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.49  cnf(c_0_25, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_14])).
% 0.18/0.49  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.49  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.49  cnf(c_0_28, plain, (r2_hidden(esk1_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.49  cnf(c_0_29, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_30, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.49  cnf(c_0_31, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.49  cnf(c_0_32, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.49  cnf(c_0_33, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.49  cnf(c_0_34, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.49  cnf(c_0_35, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_23])).
% 0.18/0.49  fof(c_0_36, plain, ![X36, X37, X38, X39, X40, X41, X42, X43, X44, X45, X46, X47, X48, X49]:(((~r2_hidden(X42,X41)|(X42=X36|X42=X37|X42=X38|X42=X39|X42=X40)|X41!=k3_enumset1(X36,X37,X38,X39,X40))&(((((X43!=X36|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40))&(X43!=X37|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40)))&(X43!=X38|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40)))&(X43!=X39|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40)))&(X43!=X40|r2_hidden(X43,X41)|X41!=k3_enumset1(X36,X37,X38,X39,X40))))&((((((esk2_6(X44,X45,X46,X47,X48,X49)!=X44|~r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48))&(esk2_6(X44,X45,X46,X47,X48,X49)!=X45|~r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48)))&(esk2_6(X44,X45,X46,X47,X48,X49)!=X46|~r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48)))&(esk2_6(X44,X45,X46,X47,X48,X49)!=X47|~r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48)))&(esk2_6(X44,X45,X46,X47,X48,X49)!=X48|~r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)|X49=k3_enumset1(X44,X45,X46,X47,X48)))&(r2_hidden(esk2_6(X44,X45,X46,X47,X48,X49),X49)|(esk2_6(X44,X45,X46,X47,X48,X49)=X44|esk2_6(X44,X45,X46,X47,X48,X49)=X45|esk2_6(X44,X45,X46,X47,X48,X49)=X46|esk2_6(X44,X45,X46,X47,X48,X49)=X47|esk2_6(X44,X45,X46,X47,X48,X49)=X48)|X49=k3_enumset1(X44,X45,X46,X47,X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.18/0.49  cnf(c_0_37, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.18/0.49  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.18/0.49  cnf(c_0_39, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|r2_hidden(esk1_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.18/0.49  cnf(c_0_40, negated_conjecture, (k2_relat_1(esk7_0)!=k1_tarski(k1_funct_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.49  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_27])])).
% 0.18/0.49  cnf(c_0_42, plain, (X1=X3|X1=X4|X1=X5|X1=X6|X1=X7|~r2_hidden(X1,X2)|X2!=k3_enumset1(X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.49  cnf(c_0_43, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),k2_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_26]), c_0_27])])).
% 0.18/0.49  cnf(c_0_44, negated_conjecture, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k2_relat_1(esk7_0)|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.49  cnf(c_0_45, negated_conjecture, (k2_relat_1(esk7_0)!=k5_enumset1(k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0),k1_funct_1(esk7_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.18/0.49  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1)))=esk1_2(k2_relat_1(esk7_0),X1)|k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k2_relat_1(esk7_0)|k2_relat_1(esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 0.18/0.49  cnf(c_0_47, plain, (X1=X7|X1=X6|X1=X5|X1=X4|X1=X3|X2!=k5_enumset1(X3,X3,X3,X4,X5,X6,X7)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_33]), c_0_34])).
% 0.18/0.49  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk7_0)=k1_tarski(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.49  cnf(c_0_49, negated_conjecture, (k5_enumset1(X1,X1,X1,X1,X1,X1,X1)=k2_relat_1(esk7_0)|k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),X1))),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.49  cnf(c_0_50, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))))=esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))|k2_relat_1(esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.49  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.49  cnf(c_0_52, plain, (X1=X2|X1=X3|X1=X4|X1=X5|X1=X6|~r2_hidden(X1,k5_enumset1(X6,X6,X6,X5,X4,X3,X2))), inference(er,[status(thm)],[c_0_47])).
% 0.18/0.49  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk7_0)=k5_enumset1(esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.18/0.49  cnf(c_0_54, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)),k2_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_45])).
% 0.18/0.49  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k5_enumset1(X4,X4,X4,X5,X6,X7,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_33]), c_0_34])).
% 0.18/0.49  cnf(c_0_56, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.49  cnf(c_0_57, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0|r2_hidden(esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_38, c_0_54])).
% 0.18/0.49  fof(c_0_58, plain, ![X29, X30]:((k2_zfmisc_1(X29,X30)!=k1_xboole_0|(X29=k1_xboole_0|X30=k1_xboole_0))&((X29!=k1_xboole_0|k2_zfmisc_1(X29,X30)=k1_xboole_0)&(X30!=k1_xboole_0|k2_zfmisc_1(X29,X30)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.49  cnf(c_0_59, plain, (r2_hidden(X1,k5_enumset1(X2,X2,X2,X3,X4,X5,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).
% 0.18/0.49  cnf(c_0_60, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk1_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.49  cnf(c_0_61, negated_conjecture, (esk3_3(esk7_0,k2_relat_1(esk7_0),esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0)))=esk6_0|k2_relat_1(esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.18/0.49  fof(c_0_62, plain, ![X31, X32]:~r2_hidden(X31,k2_zfmisc_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.18/0.49  cnf(c_0_63, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.49  cnf(c_0_64, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_59, c_0_53])).
% 0.18/0.49  cnf(c_0_65, plain, (X1=k1_xboole_0|X1=k5_enumset1(X2,X2,X2,X2,X2,X2,X2)|esk1_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_29]), c_0_30]), c_0_31]), c_0_32]), c_0_33]), c_0_34])).
% 0.18/0.49  cnf(c_0_66, negated_conjecture, (esk1_2(k2_relat_1(esk7_0),k1_funct_1(esk7_0,esk6_0))=k1_funct_1(esk7_0,esk6_0)|k2_relat_1(esk7_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_61])).
% 0.18/0.49  cnf(c_0_67, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.49  cnf(c_0_68, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_63])).
% 0.18/0.49  cnf(c_0_69, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_43, c_0_64])).
% 0.18/0.49  cnf(c_0_70, negated_conjecture, (k2_relat_1(esk7_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_45])).
% 0.18/0.49  cnf(c_0_71, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.18/0.49  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_71]), ['proof']).
% 0.18/0.49  # SZS output end CNFRefutation
% 0.18/0.49  # Proof object total steps             : 73
% 0.18/0.49  # Proof object clause steps            : 48
% 0.18/0.49  # Proof object formula steps           : 25
% 0.18/0.49  # Proof object conjectures             : 25
% 0.18/0.49  # Proof object clause conjectures      : 22
% 0.18/0.49  # Proof object formula conjectures     : 3
% 0.18/0.49  # Proof object initial clauses used    : 19
% 0.18/0.49  # Proof object initial formulas used   : 12
% 0.18/0.49  # Proof object generating inferences   : 16
% 0.18/0.49  # Proof object simplifying inferences  : 46
% 0.18/0.49  # Training examples: 0 positive, 0 negative
% 0.18/0.49  # Parsed axioms                        : 13
% 0.18/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.49  # Initial clauses                      : 36
% 0.18/0.49  # Removed in clause preprocessing      : 6
% 0.18/0.49  # Initial clauses in saturation        : 30
% 0.18/0.49  # Processed clauses                    : 937
% 0.18/0.49  # ...of these trivial                  : 0
% 0.18/0.49  # ...subsumed                          : 570
% 0.18/0.49  # ...remaining for further processing  : 367
% 0.18/0.49  # Other redundant clauses eliminated   : 762
% 0.18/0.49  # Clauses deleted for lack of memory   : 0
% 0.18/0.49  # Backward-subsumed                    : 9
% 0.18/0.49  # Backward-rewritten                   : 241
% 0.18/0.49  # Generated clauses                    : 4956
% 0.18/0.49  # ...of the previous two non-trivial   : 3964
% 0.18/0.49  # Contextual simplify-reflections      : 33
% 0.18/0.49  # Paramodulations                      : 3937
% 0.18/0.49  # Factorizations                       : 256
% 0.18/0.49  # Equation resolutions                 : 769
% 0.18/0.49  # Propositional unsat checks           : 0
% 0.18/0.49  #    Propositional check models        : 0
% 0.18/0.49  #    Propositional check unsatisfiable : 0
% 0.18/0.49  #    Propositional clauses             : 0
% 0.18/0.49  #    Propositional clauses after purity: 0
% 0.18/0.49  #    Propositional unsat core size     : 0
% 0.18/0.49  #    Propositional preprocessing time  : 0.000
% 0.18/0.49  #    Propositional encoding time       : 0.000
% 0.18/0.49  #    Propositional solver time         : 0.000
% 0.18/0.49  #    Success case prop preproc time    : 0.000
% 0.18/0.49  #    Success case prop encoding time   : 0.000
% 0.18/0.49  #    Success case prop solver time     : 0.000
% 0.18/0.49  # Current number of processed clauses  : 76
% 0.18/0.49  #    Positive orientable unit clauses  : 12
% 0.18/0.49  #    Positive unorientable unit clauses: 0
% 0.18/0.49  #    Negative unit clauses             : 2
% 0.18/0.49  #    Non-unit-clauses                  : 62
% 0.18/0.49  # Current number of unprocessed clauses: 2936
% 0.18/0.49  # ...number of literals in the above   : 18799
% 0.18/0.49  # Current number of archived formulas  : 0
% 0.18/0.49  # Current number of archived clauses   : 286
% 0.18/0.49  # Clause-clause subsumption calls (NU) : 16800
% 0.18/0.49  # Rec. Clause-clause subsumption calls : 2151
% 0.18/0.49  # Non-unit clause-clause subsumptions  : 557
% 0.18/0.49  # Unit Clause-clause subsumption calls : 47
% 0.18/0.49  # Rewrite failures with RHS unbound    : 0
% 0.18/0.49  # BW rewrite match attempts            : 25
% 0.18/0.49  # BW rewrite match successes           : 2
% 0.18/0.49  # Condensation attempts                : 0
% 0.18/0.49  # Condensation successes               : 0
% 0.18/0.49  # Termbank termtop insertions          : 113818
% 0.18/0.49  
% 0.18/0.49  # -------------------------------------------------
% 0.18/0.49  # User time                : 0.160 s
% 0.18/0.49  # System time              : 0.002 s
% 0.18/0.49  # Total time               : 0.162 s
% 0.18/0.49  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
