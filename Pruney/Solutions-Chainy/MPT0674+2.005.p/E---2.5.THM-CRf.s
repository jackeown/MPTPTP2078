%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 127 expanded)
%              Number of clauses        :   33 (  51 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  190 ( 367 expanded)
%              Number of equality atoms :   85 ( 152 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(d2_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( X5 = k2_enumset1(X1,X2,X3,X4)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X6 != X1
              & X6 != X2
              & X6 != X3
              & X6 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

fof(c_0_12,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk4_0,k1_relat_1(esk5_0))
    & k11_relat_1(esk5_0,esk4_0) != k1_tarski(k1_funct_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X14,X15] : k1_enumset1(X14,X14,X15) = k2_tarski(X14,X15) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X16,X17,X18] : k2_enumset1(X16,X16,X17,X18) = k1_enumset1(X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X19,X20] :
      ( ( r2_hidden(esk2_2(X19,X20),X19)
        | X19 = k1_tarski(X20)
        | X19 = k1_xboole_0 )
      & ( esk2_2(X19,X20) != X20
        | X19 = k1_tarski(X20)
        | X19 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) != k1_tarski(k1_funct_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_27,plain,(
    ! [X37,X38] :
      ( ( k9_relat_1(X38,X37) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X38),X37)
        | ~ v1_relat_1(X38) )
      & ( ~ r1_xboole_0(k1_relat_1(X38),X37)
        | k9_relat_1(X38,X37) = k1_xboole_0
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

fof(c_0_28,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r2_hidden(k4_tarski(X39,X40),X41)
        | r2_hidden(X40,k11_relat_1(X41,X39))
        | ~ v1_relat_1(X41) )
      & ( ~ r2_hidden(X40,k11_relat_1(X41,X39))
        | r2_hidden(k4_tarski(X39,X40),X41)
        | ~ v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_29,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) != k2_enumset1(k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X35)
      | k11_relat_1(X35,X36) = k9_relat_1(X35,k1_tarski(X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_35,plain,(
    ! [X42,X43,X44] :
      ( ( r2_hidden(X42,k1_relat_1(X44))
        | ~ r2_hidden(k4_tarski(X42,X43),X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( X43 = k1_funct_1(X44,X42)
        | ~ r2_hidden(k4_tarski(X42,X43),X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( ~ r2_hidden(X42,k1_relat_1(X44))
        | X43 != k1_funct_1(X44,X42)
        | r2_hidden(k4_tarski(X42,X43),X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)),k11_relat_1(esk5_0,esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk4_0,X1)
    | ~ r1_xboole_0(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,k1_relat_1(X2))
    | k9_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_42,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28,X29,X30,X31,X32,X33] :
      ( ( ~ r2_hidden(X27,X26)
        | X27 = X22
        | X27 = X23
        | X27 = X24
        | X27 = X25
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( X28 != X22
        | r2_hidden(X28,X26)
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( X28 != X23
        | r2_hidden(X28,X26)
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( X28 != X24
        | r2_hidden(X28,X26)
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( X28 != X25
        | r2_hidden(X28,X26)
        | X26 != k2_enumset1(X22,X23,X24,X25) )
      & ( esk3_5(X29,X30,X31,X32,X33) != X29
        | ~ r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk3_5(X29,X30,X31,X32,X33) != X30
        | ~ r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk3_5(X29,X30,X31,X32,X33) != X31
        | ~ r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( esk3_5(X29,X30,X31,X32,X33) != X32
        | ~ r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)
        | X33 = k2_enumset1(X29,X30,X31,X32) )
      & ( r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)
        | esk3_5(X29,X30,X31,X32,X33) = X29
        | esk3_5(X29,X30,X31,X32,X33) = X30
        | esk3_5(X29,X30,X31,X32,X33) = X31
        | esk3_5(X29,X30,X31,X32,X33) = X32
        | X33 = k2_enumset1(X29,X30,X31,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).

cnf(c_0_43,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_0,esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,negated_conjecture,
    ( k9_relat_1(esk5_0,X1) != k1_xboole_0
    | ~ r2_hidden(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_38])])).

cnf(c_0_48,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X5,X6,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_21]),c_0_22]),c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)) = k1_funct_1(esk5_0,esk4_0)
    | k11_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_38])])).

cnf(c_0_52,negated_conjecture,
    ( k11_relat_1(esk5_0,X1) != k1_xboole_0
    | ~ r2_hidden(esk4_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_38])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X3,X4,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])])).

cnf(c_0_54,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:32:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t117_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 0.20/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.39  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.20/0.39  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 0.20/0.39  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.20/0.39  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.20/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.39  fof(d2_enumset1, axiom, ![X1, X2, X3, X4, X5]:(X5=k2_enumset1(X1,X2,X3,X4)<=>![X6]:(r2_hidden(X6,X5)<=>~((((X6!=X1&X6!=X2)&X6!=X3)&X6!=X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 0.20/0.39  fof(c_0_11, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t117_funct_1])).
% 0.20/0.39  fof(c_0_12, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.39  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(r2_hidden(esk4_0,k1_relat_1(esk5_0))&k11_relat_1(esk5_0,esk4_0)!=k1_tarski(k1_funct_1(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.20/0.39  fof(c_0_14, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.39  fof(c_0_15, plain, ![X14, X15]:k1_enumset1(X14,X14,X15)=k2_tarski(X14,X15), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.39  fof(c_0_16, plain, ![X16, X17, X18]:k2_enumset1(X16,X16,X17,X18)=k1_enumset1(X16,X17,X18), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.39  fof(c_0_17, plain, ![X19, X20]:((r2_hidden(esk2_2(X19,X20),X19)|(X19=k1_tarski(X20)|X19=k1_xboole_0))&(esk2_2(X19,X20)!=X20|(X19=k1_tarski(X20)|X19=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.20/0.39  cnf(c_0_18, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)!=k1_tarski(k1_funct_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_21, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.39  cnf(c_0_22, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.39  cnf(c_0_23, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_24, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_25, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_26, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.39  fof(c_0_27, plain, ![X37, X38]:((k9_relat_1(X38,X37)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X38),X37)|~v1_relat_1(X38))&(~r1_xboole_0(k1_relat_1(X38),X37)|k9_relat_1(X38,X37)=k1_xboole_0|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.20/0.39  fof(c_0_28, plain, ![X39, X40, X41]:((~r2_hidden(k4_tarski(X39,X40),X41)|r2_hidden(X40,k11_relat_1(X41,X39))|~v1_relat_1(X41))&(~r2_hidden(X40,k11_relat_1(X41,X39))|r2_hidden(k4_tarski(X39,X40),X41)|~v1_relat_1(X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)!=k2_enumset1(k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])).
% 0.20/0.39  cnf(c_0_30, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_21]), c_0_22]), c_0_23])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_32, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.39  cnf(c_0_33, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  fof(c_0_34, plain, ![X35, X36]:(~v1_relat_1(X35)|k11_relat_1(X35,X36)=k9_relat_1(X35,k1_tarski(X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.20/0.39  fof(c_0_35, plain, ![X42, X43, X44]:(((r2_hidden(X42,k1_relat_1(X44))|~r2_hidden(k4_tarski(X42,X43),X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(X43=k1_funct_1(X44,X42)|~r2_hidden(k4_tarski(X42,X43),X44)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(~r2_hidden(X42,k1_relat_1(X44))|X43!=k1_funct_1(X44,X42)|r2_hidden(k4_tarski(X42,X43),X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.39  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)=k1_xboole_0|r2_hidden(esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)),k11_relat_1(esk5_0,esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30])])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk4_0,X1)|~r1_xboole_0(X1,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 0.20/0.39  cnf(c_0_40, plain, (r1_xboole_0(X1,k1_relat_1(X2))|k9_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.39  cnf(c_0_41, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  fof(c_0_42, plain, ![X22, X23, X24, X25, X26, X27, X28, X29, X30, X31, X32, X33]:(((~r2_hidden(X27,X26)|(X27=X22|X27=X23|X27=X24|X27=X25)|X26!=k2_enumset1(X22,X23,X24,X25))&((((X28!=X22|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25))&(X28!=X23|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25)))&(X28!=X24|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25)))&(X28!=X25|r2_hidden(X28,X26)|X26!=k2_enumset1(X22,X23,X24,X25))))&(((((esk3_5(X29,X30,X31,X32,X33)!=X29|~r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32))&(esk3_5(X29,X30,X31,X32,X33)!=X30|~r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(esk3_5(X29,X30,X31,X32,X33)!=X31|~r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(esk3_5(X29,X30,X31,X32,X33)!=X32|~r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)|X33=k2_enumset1(X29,X30,X31,X32)))&(r2_hidden(esk3_5(X29,X30,X31,X32,X33),X33)|(esk3_5(X29,X30,X31,X32,X33)=X29|esk3_5(X29,X30,X31,X32,X33)=X30|esk3_5(X29,X30,X31,X32,X33)=X31|esk3_5(X29,X30,X31,X32,X33)=X32)|X33=k2_enumset1(X29,X30,X31,X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_enumset1])])])])])])).
% 0.20/0.39  cnf(c_0_43, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_44, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.39  cnf(c_0_45, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)=k1_xboole_0|r2_hidden(k4_tarski(esk4_0,esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (k9_relat_1(esk5_0,X1)!=k1_xboole_0|~r2_hidden(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_38])])).
% 0.20/0.39  cnf(c_0_48, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_21]), c_0_22]), c_0_23])).
% 0.20/0.39  cnf(c_0_49, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X5,X6,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.39  cnf(c_0_50, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_21]), c_0_22]), c_0_23])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))=k1_funct_1(esk5_0,esk4_0)|k11_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_38])])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (k11_relat_1(esk5_0,X1)!=k1_xboole_0|~r2_hidden(esk4_0,k2_enumset1(X1,X1,X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_38])])).
% 0.20/0.39  cnf(c_0_53, plain, (r2_hidden(X1,k2_enumset1(X2,X3,X4,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_49])])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_29])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 56
% 0.20/0.39  # Proof object clause steps            : 33
% 0.20/0.39  # Proof object formula steps           : 23
% 0.20/0.39  # Proof object conjectures             : 16
% 0.20/0.39  # Proof object clause conjectures      : 13
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 17
% 0.20/0.39  # Proof object initial formulas used   : 11
% 0.20/0.39  # Proof object generating inferences   : 11
% 0.20/0.39  # Proof object simplifying inferences  : 27
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 11
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 30
% 0.20/0.39  # Removed in clause preprocessing      : 3
% 0.20/0.39  # Initial clauses in saturation        : 27
% 0.20/0.39  # Processed clauses                    : 78
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 12
% 0.20/0.39  # ...remaining for further processing  : 66
% 0.20/0.39  # Other redundant clauses eliminated   : 9
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 10
% 0.20/0.39  # Generated clauses                    : 408
% 0.20/0.39  # ...of the previous two non-trivial   : 356
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 395
% 0.20/0.39  # Factorizations                       : 5
% 0.20/0.39  # Equation resolutions                 : 9
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 54
% 0.20/0.39  #    Positive orientable unit clauses  : 5
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 2
% 0.20/0.39  #    Non-unit-clauses                  : 47
% 0.20/0.39  # Current number of unprocessed clauses: 305
% 0.20/0.39  # ...number of literals in the above   : 1945
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 13
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 573
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 376
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 12
% 0.20/0.39  # Unit Clause-clause subsumption calls : 24
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 1
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 9833
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.038 s
% 0.20/0.39  # System time              : 0.008 s
% 0.20/0.39  # Total time               : 0.046 s
% 0.20/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
