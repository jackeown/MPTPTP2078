%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:50 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 308 expanded)
%              Number of clauses        :   49 ( 124 expanded)
%              Number of leaves         :   16 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  192 ( 626 expanded)
%              Number of equality atoms :   83 ( 355 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

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

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_16,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_18,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ r1_tarski(k1_relat_1(X41),X40)
      | k7_relat_1(X41,X40) = X41 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | k11_relat_1(X33,X34) = k9_relat_1(X33,k1_tarski(X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

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

fof(c_0_25,plain,(
    ! [X22,X23,X24,X25,X26] : k4_enumset1(X22,X22,X23,X24,X25,X26) = k3_enumset1(X22,X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_26,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | k2_relat_1(k7_relat_1(X36,X35)) = k9_relat_1(X36,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & k1_relat_1(esk4_0) = k1_tarski(esk3_0)
    & k2_relat_1(esk4_0) != k1_tarski(k1_funct_1(esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_28,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X30,X31] :
      ( ( r2_hidden(esk2_2(X30,X31),X30)
        | X30 = k1_tarski(X31)
        | X30 = k1_xboole_0 )
      & ( esk2_2(X30,X31) != X31
        | X30 = k1_tarski(X31)
        | X30 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

fof(c_0_31,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,X29)
        | ~ r1_tarski(k2_tarski(X27,X28),X29) )
      & ( r2_hidden(X28,X29)
        | ~ r1_tarski(k2_tarski(X27,X28),X29) )
      & ( ~ r2_hidden(X27,X29)
        | ~ r2_hidden(X28,X29)
        | r1_tarski(k2_tarski(X27,X28),X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_32,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_41,plain,(
    ! [X37,X38,X39] :
      ( ( ~ r2_hidden(k4_tarski(X37,X38),X39)
        | r2_hidden(X38,k11_relat_1(X39,X37))
        | ~ v1_relat_1(X39) )
      & ( ~ r2_hidden(X38,k11_relat_1(X39,X37))
        | r2_hidden(k4_tarski(X37,X38),X39)
        | ~ v1_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X3,X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_tarski(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk4_0,X1)) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k7_relat_1(esk4_0,k1_relat_1(esk4_0)) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | X1 = k4_enumset1(X2,X2,X2,X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

fof(c_0_50,plain,(
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

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k4_enumset1(X3,X3,X3,X3,X3,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk4_0) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(esk4_0) != k1_tarski(k1_funct_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( k9_relat_1(esk4_0,k4_enumset1(X1,X1,X1,X1,X1,X1)) = k11_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( k9_relat_1(esk4_0,k1_relat_1(esk4_0)) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,plain,
    ( k11_relat_1(X1,X2) = k4_enumset1(X3,X3,X3,X3,X3,X3)
    | k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk2_2(k11_relat_1(X1,X2),X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_57,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k2_relat_1(esk4_0) != k4_enumset1(k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk4_0) = k11_relat_1(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_55])).

cnf(c_0_61,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( k11_relat_1(esk4_0,X1) = k4_enumset1(X2,X2,X2,X2,X2,X2)
    | k11_relat_1(esk4_0,X1) = k1_xboole_0
    | r2_hidden(k4_tarski(X1,esk2_2(k11_relat_1(esk4_0,X1),X2)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_39])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_64,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_29])).

cnf(c_0_66,negated_conjecture,
    ( k4_enumset1(k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0)) != k11_relat_1(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k11_relat_1(esk4_0,X1) = k4_enumset1(X2,X2,X2,X2,X2,X2)
    | esk2_2(k11_relat_1(esk4_0,X1),X2) = k1_funct_1(esk4_0,X1)
    | k11_relat_1(esk4_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_39])])).

fof(c_0_68,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_69,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk4_0,esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_63]),c_0_39])])).

cnf(c_0_71,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_72,negated_conjecture,
    ( esk2_2(k11_relat_1(esk4_0,X1),k1_funct_1(esk4_0,esk3_0)) = k1_funct_1(esk4_0,X1)
    | k11_relat_1(esk4_0,X1) = k1_xboole_0
    | k11_relat_1(esk4_0,X1) != k11_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,esk3_0),k11_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_39])])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | X1 = k4_enumset1(X2,X2,X2,X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_76,negated_conjecture,
    ( esk2_2(k11_relat_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0)) = k1_funct_1(esk4_0,esk3_0)
    | k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(k11_relat_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_66])).

cnf(c_0_79,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:09:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.47  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.18/0.47  # and selection function SelectCQArNTNpEqFirst.
% 0.18/0.47  #
% 0.18/0.47  # Preprocessing time       : 0.028 s
% 0.18/0.47  # Presaturation interreduction done
% 0.18/0.47  
% 0.18/0.47  # Proof found!
% 0.18/0.47  # SZS status Theorem
% 0.18/0.47  # SZS output start CNFRefutation
% 0.18/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.47  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.18/0.47  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 0.18/0.47  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.18/0.47  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.47  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.47  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.47  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.47  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.47  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.18/0.47  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.18/0.47  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.18/0.47  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 0.18/0.47  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.18/0.47  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.47  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.47  fof(c_0_16, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.47  fof(c_0_17, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.18/0.47  fof(c_0_18, plain, ![X40, X41]:(~v1_relat_1(X41)|(~r1_tarski(k1_relat_1(X41),X40)|k7_relat_1(X41,X40)=X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.18/0.47  cnf(c_0_19, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.47  fof(c_0_20, plain, ![X33, X34]:(~v1_relat_1(X33)|k11_relat_1(X33,X34)=k9_relat_1(X33,k1_tarski(X34))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.18/0.47  fof(c_0_21, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.47  fof(c_0_22, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.47  fof(c_0_23, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.47  fof(c_0_24, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.47  fof(c_0_25, plain, ![X22, X23, X24, X25, X26]:k4_enumset1(X22,X22,X23,X24,X25,X26)=k3_enumset1(X22,X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.47  fof(c_0_26, plain, ![X35, X36]:(~v1_relat_1(X36)|k2_relat_1(k7_relat_1(X36,X35))=k9_relat_1(X36,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.18/0.47  fof(c_0_27, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(k1_relat_1(esk4_0)=k1_tarski(esk3_0)&k2_relat_1(esk4_0)!=k1_tarski(k1_funct_1(esk4_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.18/0.47  cnf(c_0_28, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.47  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_19])).
% 0.18/0.47  fof(c_0_30, plain, ![X30, X31]:((r2_hidden(esk2_2(X30,X31),X30)|(X30=k1_tarski(X31)|X30=k1_xboole_0))&(esk2_2(X30,X31)!=X31|(X30=k1_tarski(X31)|X30=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.18/0.47  fof(c_0_31, plain, ![X27, X28, X29]:(((r2_hidden(X27,X29)|~r1_tarski(k2_tarski(X27,X28),X29))&(r2_hidden(X28,X29)|~r1_tarski(k2_tarski(X27,X28),X29)))&(~r2_hidden(X27,X29)|~r2_hidden(X28,X29)|r1_tarski(k2_tarski(X27,X28),X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.18/0.47  cnf(c_0_32, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.47  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.47  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.47  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.47  cnf(c_0_36, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.47  cnf(c_0_37, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.47  cnf(c_0_38, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.47  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.47  cnf(c_0_40, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.18/0.47  fof(c_0_41, plain, ![X37, X38, X39]:((~r2_hidden(k4_tarski(X37,X38),X39)|r2_hidden(X38,k11_relat_1(X39,X37))|~v1_relat_1(X39))&(~r2_hidden(X38,k11_relat_1(X39,X37))|r2_hidden(k4_tarski(X37,X38),X39)|~v1_relat_1(X39))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.18/0.47  cnf(c_0_42, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.47  cnf(c_0_43, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X3,X1),X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.47  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk4_0)=k1_tarski(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.47  cnf(c_0_45, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k4_enumset1(X2,X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.47  cnf(c_0_46, negated_conjecture, (k2_relat_1(k7_relat_1(esk4_0,X1))=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.47  cnf(c_0_47, negated_conjecture, (k7_relat_1(esk4_0,k1_relat_1(esk4_0))=esk4_0), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.18/0.47  cnf(c_0_48, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.47  cnf(c_0_49, plain, (X1=k1_xboole_0|X1=k4_enumset1(X2,X2,X2,X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.47  fof(c_0_50, plain, ![X42, X43, X44]:(((r2_hidden(X42,k1_relat_1(X44))|~r2_hidden(k4_tarski(X42,X43),X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(X43=k1_funct_1(X44,X42)|~r2_hidden(k4_tarski(X42,X43),X44)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(~r2_hidden(X42,k1_relat_1(X44))|X43!=k1_funct_1(X44,X42)|r2_hidden(k4_tarski(X42,X43),X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.18/0.47  cnf(c_0_51, plain, (r2_hidden(X1,X2)|~r1_tarski(k4_enumset1(X3,X3,X3,X3,X3,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.47  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk4_0)=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.47  cnf(c_0_53, negated_conjecture, (k2_relat_1(esk4_0)!=k1_tarski(k1_funct_1(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.47  cnf(c_0_54, negated_conjecture, (k9_relat_1(esk4_0,k4_enumset1(X1,X1,X1,X1,X1,X1))=k11_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 0.18/0.47  cnf(c_0_55, negated_conjecture, (k9_relat_1(esk4_0,k1_relat_1(esk4_0))=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.47  cnf(c_0_56, plain, (k11_relat_1(X1,X2)=k4_enumset1(X3,X3,X3,X3,X3,X3)|k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk2_2(k11_relat_1(X1,X2),X3)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.18/0.47  cnf(c_0_57, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.18/0.47  cnf(c_0_58, negated_conjecture, (r2_hidden(esk3_0,X1)|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.47  cnf(c_0_59, negated_conjecture, (k2_relat_1(esk4_0)!=k4_enumset1(k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.47  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk4_0)=k11_relat_1(esk4_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_52]), c_0_55])).
% 0.18/0.47  cnf(c_0_61, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.18/0.47  cnf(c_0_62, negated_conjecture, (k11_relat_1(esk4_0,X1)=k4_enumset1(X2,X2,X2,X2,X2,X2)|k11_relat_1(esk4_0,X1)=k1_xboole_0|r2_hidden(k4_tarski(X1,esk2_2(k11_relat_1(esk4_0,X1),X2)),esk4_0)), inference(spm,[status(thm)],[c_0_56, c_0_39])).
% 0.18/0.47  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.47  cnf(c_0_64, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_57])).
% 0.18/0.47  cnf(c_0_65, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_58, c_0_29])).
% 0.18/0.47  cnf(c_0_66, negated_conjecture, (k4_enumset1(k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0))!=k11_relat_1(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.18/0.47  cnf(c_0_67, negated_conjecture, (k11_relat_1(esk4_0,X1)=k4_enumset1(X2,X2,X2,X2,X2,X2)|esk2_2(k11_relat_1(esk4_0,X1),X2)=k1_funct_1(esk4_0,X1)|k11_relat_1(esk4_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_39])])).
% 0.18/0.47  fof(c_0_68, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.47  cnf(c_0_69, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.18/0.47  cnf(c_0_70, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk4_0,esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_63]), c_0_39])])).
% 0.18/0.47  cnf(c_0_71, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.47  cnf(c_0_72, negated_conjecture, (esk2_2(k11_relat_1(esk4_0,X1),k1_funct_1(esk4_0,esk3_0))=k1_funct_1(esk4_0,X1)|k11_relat_1(esk4_0,X1)=k1_xboole_0|k11_relat_1(esk4_0,X1)!=k11_relat_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.47  cnf(c_0_73, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.18/0.47  cnf(c_0_74, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,esk3_0),k11_relat_1(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_39])])).
% 0.18/0.47  cnf(c_0_75, plain, (X1=k1_xboole_0|X1=k4_enumset1(X2,X2,X2,X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.47  cnf(c_0_76, negated_conjecture, (esk2_2(k11_relat_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0))=k1_funct_1(esk4_0,esk3_0)|k11_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_72])).
% 0.18/0.47  cnf(c_0_77, negated_conjecture, (~v1_xboole_0(k11_relat_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.18/0.47  cnf(c_0_78, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_66])).
% 0.18/0.47  cnf(c_0_79, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.47  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78]), c_0_79])]), ['proof']).
% 0.18/0.47  # SZS output end CNFRefutation
% 0.18/0.47  # Proof object total steps             : 81
% 0.18/0.47  # Proof object clause steps            : 49
% 0.18/0.47  # Proof object formula steps           : 32
% 0.18/0.47  # Proof object conjectures             : 26
% 0.18/0.47  # Proof object clause conjectures      : 23
% 0.18/0.47  # Proof object formula conjectures     : 3
% 0.18/0.47  # Proof object initial clauses used    : 22
% 0.18/0.47  # Proof object initial formulas used   : 16
% 0.18/0.47  # Proof object generating inferences   : 17
% 0.18/0.47  # Proof object simplifying inferences  : 45
% 0.18/0.47  # Training examples: 0 positive, 0 negative
% 0.18/0.47  # Parsed axioms                        : 16
% 0.18/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.47  # Initial clauses                      : 28
% 0.18/0.47  # Removed in clause preprocessing      : 5
% 0.18/0.47  # Initial clauses in saturation        : 23
% 0.18/0.47  # Processed clauses                    : 1035
% 0.18/0.47  # ...of these trivial                  : 20
% 0.18/0.47  # ...subsumed                          : 564
% 0.18/0.47  # ...remaining for further processing  : 451
% 0.18/0.47  # Other redundant clauses eliminated   : 7
% 0.18/0.47  # Clauses deleted for lack of memory   : 0
% 0.18/0.47  # Backward-subsumed                    : 91
% 0.18/0.47  # Backward-rewritten                   : 60
% 0.18/0.47  # Generated clauses                    : 5059
% 0.18/0.47  # ...of the previous two non-trivial   : 4090
% 0.18/0.47  # Contextual simplify-reflections      : 2
% 0.18/0.47  # Paramodulations                      : 5038
% 0.18/0.47  # Factorizations                       : 11
% 0.18/0.47  # Equation resolutions                 : 10
% 0.18/0.47  # Propositional unsat checks           : 0
% 0.18/0.47  #    Propositional check models        : 0
% 0.18/0.47  #    Propositional check unsatisfiable : 0
% 0.18/0.47  #    Propositional clauses             : 0
% 0.18/0.47  #    Propositional clauses after purity: 0
% 0.18/0.47  #    Propositional unsat core size     : 0
% 0.18/0.47  #    Propositional preprocessing time  : 0.000
% 0.18/0.47  #    Propositional encoding time       : 0.000
% 0.18/0.47  #    Propositional solver time         : 0.000
% 0.18/0.47  #    Success case prop preproc time    : 0.000
% 0.18/0.47  #    Success case prop encoding time   : 0.000
% 0.18/0.47  #    Success case prop solver time     : 0.000
% 0.18/0.47  # Current number of processed clauses  : 275
% 0.18/0.47  #    Positive orientable unit clauses  : 40
% 0.18/0.47  #    Positive unorientable unit clauses: 1
% 0.18/0.47  #    Negative unit clauses             : 4
% 0.18/0.47  #    Non-unit-clauses                  : 230
% 0.18/0.47  # Current number of unprocessed clauses: 2661
% 0.18/0.47  # ...number of literals in the above   : 11483
% 0.18/0.47  # Current number of archived formulas  : 0
% 0.18/0.47  # Current number of archived clauses   : 178
% 0.18/0.47  # Clause-clause subsumption calls (NU) : 9305
% 0.18/0.47  # Rec. Clause-clause subsumption calls : 2656
% 0.18/0.47  # Non-unit clause-clause subsumptions  : 544
% 0.18/0.47  # Unit Clause-clause subsumption calls : 439
% 0.18/0.47  # Rewrite failures with RHS unbound    : 0
% 0.18/0.47  # BW rewrite match attempts            : 267
% 0.18/0.47  # BW rewrite match successes           : 191
% 0.18/0.47  # Condensation attempts                : 0
% 0.18/0.47  # Condensation successes               : 0
% 0.18/0.47  # Termbank termtop insertions          : 128415
% 0.18/0.47  
% 0.18/0.47  # -------------------------------------------------
% 0.18/0.47  # User time                : 0.133 s
% 0.18/0.47  # System time              : 0.006 s
% 0.18/0.47  # Total time               : 0.139 s
% 0.18/0.47  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
