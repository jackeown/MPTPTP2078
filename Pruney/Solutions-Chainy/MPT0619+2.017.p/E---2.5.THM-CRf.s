%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:53 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 435 expanded)
%              Number of clauses        :   42 ( 172 expanded)
%              Number of leaves         :   13 ( 121 expanded)
%              Depth                    :   11
%              Number of atoms          :  189 ( 852 expanded)
%              Number of equality atoms :   99 ( 559 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(c_0_13,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | k11_relat_1(X25,X26) = k9_relat_1(X25,k1_tarski(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_14,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_15,plain,(
    ! [X13,X14] : k1_enumset1(X13,X13,X14) = k2_tarski(X13,X14) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] : k2_enumset1(X15,X15,X16,X17) = k1_enumset1(X15,X16,X17) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21] : k3_enumset1(X18,X18,X19,X20,X21) = k2_enumset1(X18,X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_19,plain,(
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

fof(c_0_20,plain,(
    ! [X38,X39,X40,X42,X43,X44,X45,X47] :
      ( ( ~ r2_hidden(X40,X39)
        | r2_hidden(k4_tarski(esk6_3(X38,X39,X40),X40),X38)
        | X39 != k2_relat_1(X38) )
      & ( ~ r2_hidden(k4_tarski(X43,X42),X38)
        | r2_hidden(X42,X39)
        | X39 != k2_relat_1(X38) )
      & ( ~ r2_hidden(esk7_2(X44,X45),X45)
        | ~ r2_hidden(k4_tarski(X47,esk7_2(X44,X45)),X44)
        | X45 = k2_relat_1(X44) )
      & ( r2_hidden(esk7_2(X44,X45),X45)
        | r2_hidden(k4_tarski(esk8_2(X44,X45),esk7_2(X44,X45)),X44)
        | X45 = k2_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_21,plain,(
    ! [X22,X23] :
      ( ( r2_hidden(esk2_2(X22,X23),X22)
        | X22 = k1_tarski(X23)
        | X22 = k1_xboole_0 )
      & ( esk2_2(X22,X23) != X23
        | X22 = k1_tarski(X23)
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

cnf(c_0_22,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_27,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & v1_funct_1(esk10_0)
    & k1_relat_1(esk10_0) = k1_tarski(esk9_0)
    & k2_relat_1(esk10_0) != k1_tarski(k1_funct_1(esk10_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_28,plain,(
    ! [X49] :
      ( ~ v1_relat_1(X49)
      | k9_relat_1(X49,k1_relat_1(X49)) = k2_relat_1(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_31,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(X29,esk3_3(X27,X28,X29)),X27)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X31,X32),X27)
        | r2_hidden(X31,X28)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(esk4_2(X33,X34),X34)
        | ~ r2_hidden(k4_tarski(esk4_2(X33,X34),X36),X33)
        | X34 = k1_relat_1(X33) )
      & ( r2_hidden(esk4_2(X33,X34),X34)
        | r2_hidden(k4_tarski(esk4_2(X33,X34),esk5_2(X33,X34)),X33)
        | X34 = k1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk10_0) = k1_tarski(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X2,X2,X2,X2,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_39,plain,
    ( X1 = X3
    | X2 != k3_enumset1(X3,X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

fof(c_0_43,plain,(
    ! [X50,X51] :
      ( ( ~ r2_hidden(X50,k1_relat_1(X51))
        | k11_relat_1(X51,X50) != k1_xboole_0
        | ~ v1_relat_1(X51) )
      & ( k11_relat_1(X51,X50) = k1_xboole_0
        | r2_hidden(X50,k1_relat_1(X51))
        | ~ v1_relat_1(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

cnf(c_0_44,negated_conjecture,
    ( k9_relat_1(esk10_0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk10_0) = k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( k9_relat_1(esk10_0,k1_relat_1(esk10_0)) = k2_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_35])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( k2_relat_1(X1) = k3_enumset1(X2,X2,X2,X2,X2)
    | k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)),esk2_2(k2_relat_1(X1),X2)),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k11_relat_1(esk10_0,esk9_0) = k2_relat_1(esk10_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( k2_relat_1(esk10_0) != k1_tarski(k1_funct_1(esk10_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk9_0
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_45])).

cnf(c_0_56,plain,
    ( k2_relat_1(X1) = k3_enumset1(X2,X2,X2,X2,X2)
    | k2_relat_1(X1) = k1_xboole_0
    | r2_hidden(esk6_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)),k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk10_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_35]),c_0_53])])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(esk10_0) != k3_enumset1(k1_funct_1(esk10_0,esk9_0),k1_funct_1(esk10_0,esk9_0),k1_funct_1(esk10_0,esk9_0),k1_funct_1(esk10_0,esk9_0),k1_funct_1(esk10_0,esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( esk6_3(esk10_0,k2_relat_1(esk10_0),esk2_2(k2_relat_1(esk10_0),X1)) = esk9_0
    | k3_enumset1(X1,X1,X1,X1,X1) = k2_relat_1(esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

fof(c_0_60,plain,(
    ! [X52,X53,X54] :
      ( ( r2_hidden(X52,k1_relat_1(X54))
        | ~ r2_hidden(k4_tarski(X52,X53),X54)
        | ~ v1_relat_1(X54)
        | ~ v1_funct_1(X54) )
      & ( X53 = k1_funct_1(X54,X52)
        | ~ r2_hidden(k4_tarski(X52,X53),X54)
        | ~ v1_relat_1(X54)
        | ~ v1_funct_1(X54) )
      & ( ~ r2_hidden(X52,k1_relat_1(X54))
        | X53 != k1_funct_1(X54,X52)
        | r2_hidden(k4_tarski(X52,X53),X54)
        | ~ v1_relat_1(X54)
        | ~ v1_funct_1(X54) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_61,negated_conjecture,
    ( esk6_3(esk10_0,k2_relat_1(esk10_0),esk2_2(k2_relat_1(esk10_0),k1_funct_1(esk10_0,esk9_0))) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk2_2(k2_relat_1(esk10_0),k1_funct_1(esk10_0,esk9_0))),esk10_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_61]),c_0_58]),c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | X1 = k3_enumset1(X2,X2,X2,X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_23]),c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_67,negated_conjecture,
    ( esk2_2(k2_relat_1(esk10_0),k1_funct_1(esk10_0,esk9_0)) = k1_funct_1(esk10_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_35])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_58]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n014.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 13:18:52 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.16/0.31  # No SInE strategy applied
% 0.16/0.31  # Trying AutoSched0 for 299 seconds
% 0.91/1.17  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.91/1.17  # and selection function SelectCQArNTNpEqFirst.
% 0.91/1.17  #
% 0.91/1.17  # Preprocessing time       : 0.028 s
% 0.91/1.17  # Presaturation interreduction done
% 0.91/1.17  
% 0.91/1.17  # Proof found!
% 0.91/1.17  # SZS status Theorem
% 0.91/1.17  # SZS output start CNFRefutation
% 0.91/1.17  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 0.91/1.17  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.91/1.17  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.91/1.17  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.91/1.17  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.91/1.17  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.91/1.17  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.91/1.17  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.91/1.17  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.91/1.17  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.91/1.17  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.91/1.17  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 0.91/1.17  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.91/1.17  fof(c_0_13, plain, ![X25, X26]:(~v1_relat_1(X25)|k11_relat_1(X25,X26)=k9_relat_1(X25,k1_tarski(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.91/1.17  fof(c_0_14, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.91/1.17  fof(c_0_15, plain, ![X13, X14]:k1_enumset1(X13,X13,X14)=k2_tarski(X13,X14), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.91/1.17  fof(c_0_16, plain, ![X15, X16, X17]:k2_enumset1(X15,X15,X16,X17)=k1_enumset1(X15,X16,X17), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.91/1.17  fof(c_0_17, plain, ![X18, X19, X20, X21]:k3_enumset1(X18,X18,X19,X20,X21)=k2_enumset1(X18,X19,X20,X21), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.91/1.17  fof(c_0_18, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.91/1.17  fof(c_0_19, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.91/1.17  fof(c_0_20, plain, ![X38, X39, X40, X42, X43, X44, X45, X47]:(((~r2_hidden(X40,X39)|r2_hidden(k4_tarski(esk6_3(X38,X39,X40),X40),X38)|X39!=k2_relat_1(X38))&(~r2_hidden(k4_tarski(X43,X42),X38)|r2_hidden(X42,X39)|X39!=k2_relat_1(X38)))&((~r2_hidden(esk7_2(X44,X45),X45)|~r2_hidden(k4_tarski(X47,esk7_2(X44,X45)),X44)|X45=k2_relat_1(X44))&(r2_hidden(esk7_2(X44,X45),X45)|r2_hidden(k4_tarski(esk8_2(X44,X45),esk7_2(X44,X45)),X44)|X45=k2_relat_1(X44)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.91/1.17  fof(c_0_21, plain, ![X22, X23]:((r2_hidden(esk2_2(X22,X23),X22)|(X22=k1_tarski(X23)|X22=k1_xboole_0))&(esk2_2(X22,X23)!=X23|(X22=k1_tarski(X23)|X22=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.91/1.17  cnf(c_0_22, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.91/1.17  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.91/1.17  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.91/1.17  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.91/1.17  cnf(c_0_26, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.91/1.17  fof(c_0_27, negated_conjecture, ((v1_relat_1(esk10_0)&v1_funct_1(esk10_0))&(k1_relat_1(esk10_0)=k1_tarski(esk9_0)&k2_relat_1(esk10_0)!=k1_tarski(k1_funct_1(esk10_0,esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.91/1.17  fof(c_0_28, plain, ![X49]:(~v1_relat_1(X49)|k9_relat_1(X49,k1_relat_1(X49))=k2_relat_1(X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.91/1.17  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.91/1.17  cnf(c_0_30, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.91/1.17  fof(c_0_31, plain, ![X27, X28, X29, X31, X32, X33, X34, X36]:(((~r2_hidden(X29,X28)|r2_hidden(k4_tarski(X29,esk3_3(X27,X28,X29)),X27)|X28!=k1_relat_1(X27))&(~r2_hidden(k4_tarski(X31,X32),X27)|r2_hidden(X31,X28)|X28!=k1_relat_1(X27)))&((~r2_hidden(esk4_2(X33,X34),X34)|~r2_hidden(k4_tarski(esk4_2(X33,X34),X36),X33)|X34=k1_relat_1(X33))&(r2_hidden(esk4_2(X33,X34),X34)|r2_hidden(k4_tarski(esk4_2(X33,X34),esk5_2(X33,X34)),X33)|X34=k1_relat_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.91/1.17  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.91/1.17  cnf(c_0_33, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.91/1.17  cnf(c_0_34, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k3_enumset1(X2,X2,X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.91/1.17  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.91/1.17  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk10_0)=k1_tarski(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.91/1.17  cnf(c_0_37, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.91/1.17  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X2,X2,X2,X2,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.91/1.17  cnf(c_0_39, plain, (X1=X3|X2!=k3_enumset1(X3,X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.91/1.17  cnf(c_0_40, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.91/1.17  cnf(c_0_41, plain, (r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_32])).
% 0.91/1.17  cnf(c_0_42, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.91/1.17  fof(c_0_43, plain, ![X50, X51]:((~r2_hidden(X50,k1_relat_1(X51))|k11_relat_1(X51,X50)!=k1_xboole_0|~v1_relat_1(X51))&(k11_relat_1(X51,X50)=k1_xboole_0|r2_hidden(X50,k1_relat_1(X51))|~v1_relat_1(X51))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 0.91/1.17  cnf(c_0_44, negated_conjecture, (k9_relat_1(esk10_0,k3_enumset1(X1,X1,X1,X1,X1))=k11_relat_1(esk10_0,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.91/1.17  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk10_0)=k3_enumset1(esk9_0,esk9_0,esk9_0,esk9_0,esk9_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.91/1.17  cnf(c_0_46, negated_conjecture, (k9_relat_1(esk10_0,k1_relat_1(esk10_0))=k2_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_37, c_0_35])).
% 0.91/1.17  cnf(c_0_47, plain, (r2_hidden(X1,k3_enumset1(X1,X1,X1,X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).
% 0.91/1.17  cnf(c_0_48, plain, (X1=X2|~r2_hidden(X1,k3_enumset1(X2,X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_39])).
% 0.91/1.17  cnf(c_0_49, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_40])).
% 0.91/1.17  cnf(c_0_50, plain, (k2_relat_1(X1)=k3_enumset1(X2,X2,X2,X2,X2)|k2_relat_1(X1)=k1_xboole_0|r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)),esk2_2(k2_relat_1(X1),X2)),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.91/1.17  cnf(c_0_51, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.91/1.17  cnf(c_0_52, negated_conjecture, (k11_relat_1(esk10_0,esk9_0)=k2_relat_1(esk10_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.91/1.17  cnf(c_0_53, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_47, c_0_45])).
% 0.91/1.17  cnf(c_0_54, negated_conjecture, (k2_relat_1(esk10_0)!=k1_tarski(k1_funct_1(esk10_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.91/1.17  cnf(c_0_55, negated_conjecture, (X1=esk9_0|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_48, c_0_45])).
% 0.91/1.17  cnf(c_0_56, plain, (k2_relat_1(X1)=k3_enumset1(X2,X2,X2,X2,X2)|k2_relat_1(X1)=k1_xboole_0|r2_hidden(esk6_3(X1,k2_relat_1(X1),esk2_2(k2_relat_1(X1),X2)),k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.91/1.17  cnf(c_0_57, negated_conjecture, (k2_relat_1(esk10_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_35]), c_0_53])])).
% 0.91/1.17  cnf(c_0_58, negated_conjecture, (k2_relat_1(esk10_0)!=k3_enumset1(k1_funct_1(esk10_0,esk9_0),k1_funct_1(esk10_0,esk9_0),k1_funct_1(esk10_0,esk9_0),k1_funct_1(esk10_0,esk9_0),k1_funct_1(esk10_0,esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.91/1.17  cnf(c_0_59, negated_conjecture, (esk6_3(esk10_0,k2_relat_1(esk10_0),esk2_2(k2_relat_1(esk10_0),X1))=esk9_0|k3_enumset1(X1,X1,X1,X1,X1)=k2_relat_1(esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.91/1.17  fof(c_0_60, plain, ![X52, X53, X54]:(((r2_hidden(X52,k1_relat_1(X54))|~r2_hidden(k4_tarski(X52,X53),X54)|(~v1_relat_1(X54)|~v1_funct_1(X54)))&(X53=k1_funct_1(X54,X52)|~r2_hidden(k4_tarski(X52,X53),X54)|(~v1_relat_1(X54)|~v1_funct_1(X54))))&(~r2_hidden(X52,k1_relat_1(X54))|X53!=k1_funct_1(X54,X52)|r2_hidden(k4_tarski(X52,X53),X54)|(~v1_relat_1(X54)|~v1_funct_1(X54)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.91/1.17  cnf(c_0_61, negated_conjecture, (esk6_3(esk10_0,k2_relat_1(esk10_0),esk2_2(k2_relat_1(esk10_0),k1_funct_1(esk10_0,esk9_0)))=esk9_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.91/1.17  cnf(c_0_62, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.91/1.17  cnf(c_0_63, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.91/1.17  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk2_2(k2_relat_1(esk10_0),k1_funct_1(esk10_0,esk9_0))),esk10_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_61]), c_0_58]), c_0_57])).
% 0.91/1.17  cnf(c_0_65, negated_conjecture, (v1_funct_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.91/1.17  cnf(c_0_66, plain, (X1=k1_xboole_0|X1=k3_enumset1(X2,X2,X2,X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_23]), c_0_24]), c_0_25]), c_0_26])).
% 0.91/1.17  cnf(c_0_67, negated_conjecture, (esk2_2(k2_relat_1(esk10_0),k1_funct_1(esk10_0,esk9_0))=k1_funct_1(esk10_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_35])])).
% 0.91/1.17  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_58]), c_0_57]), ['proof']).
% 0.91/1.17  # SZS output end CNFRefutation
% 0.91/1.17  # Proof object total steps             : 69
% 0.91/1.17  # Proof object clause steps            : 42
% 0.91/1.17  # Proof object formula steps           : 27
% 0.91/1.17  # Proof object conjectures             : 20
% 0.91/1.17  # Proof object clause conjectures      : 17
% 0.91/1.17  # Proof object formula conjectures     : 3
% 0.91/1.17  # Proof object initial clauses used    : 18
% 0.91/1.17  # Proof object initial formulas used   : 13
% 0.91/1.17  # Proof object generating inferences   : 13
% 0.91/1.17  # Proof object simplifying inferences  : 45
% 0.91/1.17  # Training examples: 0 positive, 0 negative
% 0.91/1.17  # Parsed axioms                        : 13
% 0.91/1.17  # Removed by relevancy pruning/SinE    : 0
% 0.91/1.17  # Initial clauses                      : 29
% 0.91/1.17  # Removed in clause preprocessing      : 4
% 0.91/1.17  # Initial clauses in saturation        : 25
% 0.91/1.17  # Processed clauses                    : 3016
% 0.91/1.17  # ...of these trivial                  : 0
% 0.91/1.17  # ...subsumed                          : 1896
% 0.91/1.17  # ...remaining for further processing  : 1120
% 0.91/1.17  # Other redundant clauses eliminated   : 616
% 0.91/1.17  # Clauses deleted for lack of memory   : 0
% 0.91/1.17  # Backward-subsumed                    : 68
% 0.91/1.17  # Backward-rewritten                   : 6
% 0.91/1.17  # Generated clauses                    : 52301
% 0.91/1.17  # ...of the previous two non-trivial   : 50363
% 0.91/1.17  # Contextual simplify-reflections      : 26
% 0.91/1.17  # Paramodulations                      : 51570
% 0.91/1.17  # Factorizations                       : 116
% 0.91/1.17  # Equation resolutions                 : 616
% 0.91/1.17  # Propositional unsat checks           : 0
% 0.91/1.17  #    Propositional check models        : 0
% 0.91/1.17  #    Propositional check unsatisfiable : 0
% 0.91/1.17  #    Propositional clauses             : 0
% 0.91/1.17  #    Propositional clauses after purity: 0
% 0.91/1.17  #    Propositional unsat core size     : 0
% 0.91/1.17  #    Propositional preprocessing time  : 0.000
% 0.91/1.17  #    Propositional encoding time       : 0.000
% 0.91/1.17  #    Propositional solver time         : 0.000
% 0.91/1.17  #    Success case prop preproc time    : 0.000
% 0.91/1.17  #    Success case prop encoding time   : 0.000
% 0.91/1.17  #    Success case prop solver time     : 0.000
% 0.91/1.17  # Current number of processed clauses  : 1015
% 0.91/1.17  #    Positive orientable unit clauses  : 21
% 0.91/1.17  #    Positive unorientable unit clauses: 0
% 0.91/1.17  #    Negative unit clauses             : 2
% 0.91/1.17  #    Non-unit-clauses                  : 992
% 0.91/1.17  # Current number of unprocessed clauses: 47087
% 0.91/1.17  # ...number of literals in the above   : 310040
% 0.91/1.17  # Current number of archived formulas  : 0
% 0.91/1.17  # Current number of archived clauses   : 102
% 0.91/1.17  # Clause-clause subsumption calls (NU) : 156382
% 0.91/1.17  # Rec. Clause-clause subsumption calls : 19360
% 0.91/1.17  # Non-unit clause-clause subsumptions  : 1977
% 0.91/1.17  # Unit Clause-clause subsumption calls : 1443
% 0.91/1.17  # Rewrite failures with RHS unbound    : 0
% 0.91/1.17  # BW rewrite match attempts            : 33
% 0.91/1.17  # BW rewrite match successes           : 3
% 0.91/1.17  # Condensation attempts                : 0
% 0.91/1.17  # Condensation successes               : 0
% 0.91/1.17  # Termbank termtop insertions          : 1519621
% 0.91/1.17  
% 0.91/1.17  # -------------------------------------------------
% 0.91/1.17  # User time                : 0.840 s
% 0.91/1.17  # System time              : 0.024 s
% 0.91/1.17  # Total time               : 0.864 s
% 0.91/1.17  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
