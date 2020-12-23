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
% DateTime   : Thu Dec  3 10:52:53 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 315 expanded)
%              Number of clauses        :   40 ( 125 expanded)
%              Number of leaves         :   11 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  175 ( 646 expanded)
%              Number of equality atoms :   82 ( 389 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_14,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

cnf(c_0_16,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & k1_relat_1(esk5_0) = k1_tarski(esk4_0)
    & k2_relat_1(esk5_0) != k1_tarski(k1_funct_1(esk5_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_tarski(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_23,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | k11_relat_1(X21,X22) = k9_relat_1(X21,k1_tarski(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(esk5_0) = k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_17]),c_0_18]),c_0_19])).

fof(c_0_26,plain,(
    ! [X23,X24,X25,X27] :
      ( ( r2_hidden(esk3_3(X23,X24,X25),k1_relat_1(X25))
        | ~ r2_hidden(X23,k9_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(k4_tarski(esk3_3(X23,X24,X25),X23),X25)
        | ~ r2_hidden(X23,k9_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk3_3(X23,X24,X25),X24)
        | ~ r2_hidden(X23,k9_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(X27,k1_relat_1(X25))
        | ~ r2_hidden(k4_tarski(X27,X23),X25)
        | ~ r2_hidden(X27,X24)
        | r2_hidden(X23,k9_relat_1(X25,X24))
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_27,plain,(
    ! [X18,X19] :
      ( ( r2_hidden(esk2_2(X18,X19),X18)
        | X18 = k1_tarski(X19)
        | X18 = k1_xboole_0 )
      & ( esk2_2(X18,X19) != X19
        | X18 = k1_tarski(X19)
        | X18 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

cnf(c_0_28,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk5_0) != k1_tarski(k1_funct_1(esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | k9_relat_1(X28,k1_relat_1(X28)) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_35,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( esk3_3(X1,X2,esk5_0) = esk4_0
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( k2_relat_1(esk5_0) != k2_enumset1(k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_40,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k9_relat_1(X1,k1_relat_1(esk5_0)) = k11_relat_1(X1,esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_25])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,X1),esk5_0)
    | ~ r2_hidden(X1,k9_relat_1(esk5_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31])])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | r2_hidden(esk2_2(k2_relat_1(esk5_0),k1_funct_1(esk5_0,esk4_0)),k2_relat_1(esk5_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(esk5_0) = k11_relat_1(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31])])).

fof(c_0_45,plain,(
    ! [X31,X32,X33] :
      ( ( r2_hidden(X31,k1_relat_1(X33))
        | ~ r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( X32 = k1_funct_1(X33,X31)
        | ~ r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( ~ r2_hidden(X31,k1_relat_1(X33))
        | X32 != k1_funct_1(X33,X31)
        | r2_hidden(k4_tarski(X31,X32),X33)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,X1),esk5_0)
    | ~ r2_hidden(X1,k11_relat_1(esk5_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_31])])).

cnf(c_0_47,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) = k1_xboole_0
    | r2_hidden(esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)),k11_relat_1(esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_44]),c_0_44])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_49,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_50,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_0,esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))),esk5_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_17]),c_0_18]),c_0_19])).

fof(c_0_54,plain,(
    ! [X29,X30] :
      ( ( ~ r2_hidden(X29,k1_relat_1(X30))
        | k11_relat_1(X30,X29) != k1_xboole_0
        | ~ v1_relat_1(X30) )
      & ( k11_relat_1(X30,X29) = k1_xboole_0
        | r2_hidden(X29,k1_relat_1(X30))
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_17]),c_0_18]),c_0_19])).

cnf(c_0_56,negated_conjecture,
    ( esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)) = k1_funct_1(esk5_0,esk4_0)
    | k11_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_31])])).

cnf(c_0_57,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)) != k11_relat_1(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k11_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_25])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_31]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:58:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.18/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.18/0.39  #
% 0.18/0.39  # Preprocessing time       : 0.028 s
% 0.18/0.39  
% 0.18/0.39  # Proof found!
% 0.18/0.39  # SZS status Theorem
% 0.18/0.39  # SZS output start CNFRefutation
% 0.18/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.18/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.39  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.39  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.18/0.39  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.18/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 0.18/0.39  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.18/0.39  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.18/0.39  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.18/0.39  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 0.18/0.39  fof(c_0_11, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.18/0.39  fof(c_0_12, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.39  fof(c_0_13, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.39  fof(c_0_14, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.18/0.39  cnf(c_0_16, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.39  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.39  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.39  cnf(c_0_19, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.39  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(k1_relat_1(esk5_0)=k1_tarski(esk4_0)&k2_relat_1(esk5_0)!=k1_tarski(k1_funct_1(esk5_0,esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.18/0.39  cnf(c_0_21, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])).
% 0.18/0.39  cnf(c_0_22, negated_conjecture, (k1_relat_1(esk5_0)=k1_tarski(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  fof(c_0_23, plain, ![X21, X22]:(~v1_relat_1(X21)|k11_relat_1(X21,X22)=k9_relat_1(X21,k1_tarski(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.18/0.39  cnf(c_0_24, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.18/0.39  cnf(c_0_25, negated_conjecture, (k1_relat_1(esk5_0)=k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_17]), c_0_18]), c_0_19])).
% 0.18/0.39  fof(c_0_26, plain, ![X23, X24, X25, X27]:((((r2_hidden(esk3_3(X23,X24,X25),k1_relat_1(X25))|~r2_hidden(X23,k9_relat_1(X25,X24))|~v1_relat_1(X25))&(r2_hidden(k4_tarski(esk3_3(X23,X24,X25),X23),X25)|~r2_hidden(X23,k9_relat_1(X25,X24))|~v1_relat_1(X25)))&(r2_hidden(esk3_3(X23,X24,X25),X24)|~r2_hidden(X23,k9_relat_1(X25,X24))|~v1_relat_1(X25)))&(~r2_hidden(X27,k1_relat_1(X25))|~r2_hidden(k4_tarski(X27,X23),X25)|~r2_hidden(X27,X24)|r2_hidden(X23,k9_relat_1(X25,X24))|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.18/0.39  fof(c_0_27, plain, ![X18, X19]:((r2_hidden(esk2_2(X18,X19),X18)|(X18=k1_tarski(X19)|X18=k1_xboole_0))&(esk2_2(X18,X19)!=X19|(X18=k1_tarski(X19)|X18=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.18/0.39  cnf(c_0_28, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.39  cnf(c_0_29, negated_conjecture, (X1=esk4_0|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.18/0.39  cnf(c_0_30, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_32, negated_conjecture, (k2_relat_1(esk5_0)!=k1_tarski(k1_funct_1(esk5_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_33, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.39  fof(c_0_34, plain, ![X28]:(~v1_relat_1(X28)|k9_relat_1(X28,k1_relat_1(X28))=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.18/0.39  cnf(c_0_35, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_enumset1(X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_17]), c_0_18]), c_0_19])).
% 0.18/0.39  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk3_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.39  cnf(c_0_37, negated_conjecture, (esk3_3(X1,X2,esk5_0)=esk4_0|~r2_hidden(X1,k9_relat_1(esk5_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.18/0.39  cnf(c_0_38, negated_conjecture, (k2_relat_1(esk5_0)!=k2_enumset1(k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_17]), c_0_18]), c_0_19])).
% 0.18/0.39  cnf(c_0_39, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_17]), c_0_18]), c_0_19])).
% 0.18/0.39  cnf(c_0_40, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.39  cnf(c_0_41, negated_conjecture, (k9_relat_1(X1,k1_relat_1(esk5_0))=k11_relat_1(X1,esk4_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_25])).
% 0.18/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,X1),esk5_0)|~r2_hidden(X1,k9_relat_1(esk5_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_31])])).
% 0.18/0.39  cnf(c_0_43, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0|r2_hidden(esk2_2(k2_relat_1(esk5_0),k1_funct_1(esk5_0,esk4_0)),k2_relat_1(esk5_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39])])).
% 0.18/0.39  cnf(c_0_44, negated_conjecture, (k2_relat_1(esk5_0)=k11_relat_1(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_31])])).
% 0.18/0.39  fof(c_0_45, plain, ![X31, X32, X33]:(((r2_hidden(X31,k1_relat_1(X33))|~r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(X32=k1_funct_1(X33,X31)|~r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33))))&(~r2_hidden(X31,k1_relat_1(X33))|X32!=k1_funct_1(X33,X31)|r2_hidden(k4_tarski(X31,X32),X33)|(~v1_relat_1(X33)|~v1_funct_1(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.18/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,X1),esk5_0)|~r2_hidden(X1,k11_relat_1(esk5_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_31])])).
% 0.18/0.39  cnf(c_0_47, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)=k1_xboole_0|r2_hidden(esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0)),k11_relat_1(esk5_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_44]), c_0_44])).
% 0.18/0.39  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.39  cnf(c_0_49, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.39  cnf(c_0_50, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.39  cnf(c_0_51, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)=k1_xboole_0|r2_hidden(k4_tarski(esk4_0,esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))),esk5_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.18/0.39  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.39  cnf(c_0_53, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_17]), c_0_18]), c_0_19])).
% 0.18/0.39  fof(c_0_54, plain, ![X29, X30]:((~r2_hidden(X29,k1_relat_1(X30))|k11_relat_1(X30,X29)!=k1_xboole_0|~v1_relat_1(X30))&(k11_relat_1(X30,X29)=k1_xboole_0|r2_hidden(X29,k1_relat_1(X30))|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.18/0.39  cnf(c_0_55, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_17]), c_0_18]), c_0_19])).
% 0.18/0.39  cnf(c_0_56, negated_conjecture, (esk2_2(k11_relat_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))=k1_funct_1(esk5_0,esk4_0)|k11_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_31])])).
% 0.18/0.39  cnf(c_0_57, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0),k1_funct_1(esk5_0,esk4_0))!=k11_relat_1(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_38, c_0_44])).
% 0.18/0.39  cnf(c_0_58, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 0.18/0.39  cnf(c_0_59, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.39  cnf(c_0_60, negated_conjecture, (k11_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.18/0.39  cnf(c_0_61, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_58, c_0_25])).
% 0.18/0.39  cnf(c_0_62, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_31]), c_0_61])]), ['proof']).
% 0.18/0.39  # SZS output end CNFRefutation
% 0.18/0.39  # Proof object total steps             : 63
% 0.18/0.39  # Proof object clause steps            : 40
% 0.18/0.39  # Proof object formula steps           : 23
% 0.18/0.39  # Proof object conjectures             : 23
% 0.18/0.39  # Proof object clause conjectures      : 20
% 0.18/0.39  # Proof object formula conjectures     : 3
% 0.18/0.39  # Proof object initial clauses used    : 17
% 0.18/0.39  # Proof object initial formulas used   : 11
% 0.18/0.39  # Proof object generating inferences   : 12
% 0.18/0.39  # Proof object simplifying inferences  : 44
% 0.18/0.39  # Training examples: 0 positive, 0 negative
% 0.18/0.39  # Parsed axioms                        : 11
% 0.18/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.39  # Initial clauses                      : 24
% 0.18/0.39  # Removed in clause preprocessing      : 3
% 0.18/0.39  # Initial clauses in saturation        : 21
% 0.18/0.39  # Processed clauses                    : 129
% 0.18/0.39  # ...of these trivial                  : 2
% 0.18/0.39  # ...subsumed                          : 23
% 0.18/0.39  # ...remaining for further processing  : 104
% 0.18/0.39  # Other redundant clauses eliminated   : 40
% 0.18/0.39  # Clauses deleted for lack of memory   : 0
% 0.18/0.39  # Backward-subsumed                    : 6
% 0.18/0.39  # Backward-rewritten                   : 17
% 0.18/0.39  # Generated clauses                    : 1070
% 0.18/0.39  # ...of the previous two non-trivial   : 936
% 0.18/0.39  # Contextual simplify-reflections      : 6
% 0.18/0.39  # Paramodulations                      : 1017
% 0.18/0.39  # Factorizations                       : 14
% 0.18/0.39  # Equation resolutions                 : 40
% 0.18/0.39  # Propositional unsat checks           : 0
% 0.18/0.39  #    Propositional check models        : 0
% 0.18/0.39  #    Propositional check unsatisfiable : 0
% 0.18/0.39  #    Propositional clauses             : 0
% 0.18/0.39  #    Propositional clauses after purity: 0
% 0.18/0.39  #    Propositional unsat core size     : 0
% 0.18/0.39  #    Propositional preprocessing time  : 0.000
% 0.18/0.39  #    Propositional encoding time       : 0.000
% 0.18/0.39  #    Propositional solver time         : 0.000
% 0.18/0.39  #    Success case prop preproc time    : 0.000
% 0.18/0.39  #    Success case prop encoding time   : 0.000
% 0.18/0.39  #    Success case prop solver time     : 0.000
% 0.18/0.39  # Current number of processed clauses  : 78
% 0.18/0.39  #    Positive orientable unit clauses  : 7
% 0.18/0.39  #    Positive unorientable unit clauses: 0
% 0.18/0.39  #    Negative unit clauses             : 0
% 0.18/0.39  #    Non-unit-clauses                  : 71
% 0.18/0.39  # Current number of unprocessed clauses: 771
% 0.18/0.39  # ...number of literals in the above   : 4267
% 0.18/0.39  # Current number of archived formulas  : 0
% 0.18/0.39  # Current number of archived clauses   : 26
% 0.18/0.39  # Clause-clause subsumption calls (NU) : 587
% 0.18/0.39  # Rec. Clause-clause subsumption calls : 286
% 0.18/0.39  # Non-unit clause-clause subsumptions  : 33
% 0.18/0.39  # Unit Clause-clause subsumption calls : 26
% 0.18/0.39  # Rewrite failures with RHS unbound    : 0
% 0.18/0.39  # BW rewrite match attempts            : 5
% 0.18/0.39  # BW rewrite match successes           : 4
% 0.18/0.39  # Condensation attempts                : 0
% 0.18/0.39  # Condensation successes               : 0
% 0.18/0.39  # Termbank termtop insertions          : 17172
% 0.18/0.39  
% 0.18/0.39  # -------------------------------------------------
% 0.18/0.39  # User time                : 0.059 s
% 0.18/0.39  # System time              : 0.001 s
% 0.18/0.39  # Total time               : 0.060 s
% 0.18/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
