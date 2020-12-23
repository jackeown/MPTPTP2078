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
% DateTime   : Thu Dec  3 10:54:24 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 238 expanded)
%              Number of clauses        :   50 ( 106 expanded)
%              Number of leaves         :   10 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  199 ( 762 expanded)
%              Number of equality atoms :   50 ( 148 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t12_zfmisc_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(l44_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ( ~ r1_tarski(k1_tarski(X11),X12)
        | r2_hidden(X11,X12) )
      & ( ~ r2_hidden(X11,X12)
        | r1_tarski(k1_tarski(X11),X12) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_11,plain,(
    ! [X10] : k2_tarski(X10,X10) = k1_tarski(X10) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X16,X17] : r1_tarski(k1_tarski(X16),k2_tarski(X16,X17)) ),
    inference(variable_rename,[status(thm)],[t12_zfmisc_1])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X4,X5,X7,X8,X9] :
      ( ( r2_hidden(esk1_2(X4,X5),X4)
        | r1_xboole_0(X4,X5) )
      & ( r2_hidden(esk1_2(X4,X5),X5)
        | r1_xboole_0(X4,X5) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | ~ r1_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,k2_tarski(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

fof(c_0_25,plain,(
    ! [X22,X23,X24] :
      ( ( ~ r2_hidden(k4_tarski(X22,X23),X24)
        | r2_hidden(X23,k11_relat_1(X24,X22))
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(X23,k11_relat_1(X24,X22))
        | r2_hidden(k4_tarski(X22,X23),X24)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

fof(c_0_26,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( X26 = k1_funct_1(X27,X25)
        | ~ r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( ~ r2_hidden(X25,k1_relat_1(X27))
        | X26 != k1_funct_1(X27,X25)
        | r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ r1_xboole_0(k11_relat_1(X1,X2),k11_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_35,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk3_0,k1_relat_1(esk4_0))
    & k11_relat_1(esk4_0,esk3_0) != k1_tarski(k1_funct_1(esk4_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).

cnf(c_0_36,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,esk1_2(X2,k11_relat_1(X3,X1))),X3)
    | r1_xboole_0(X2,k11_relat_1(X3,X1))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_xboole_0(k11_relat_1(X1,X2),k11_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,k1_relat_1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( esk1_2(X1,k11_relat_1(X2,X3)) = k1_funct_1(X2,X3)
    | r1_xboole_0(X1,k11_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_43,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | k11_relat_1(X18,X19) = k9_relat_1(X18,k1_tarski(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_xboole_0(k11_relat_1(esk4_0,esk3_0),k11_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_45,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | r1_xboole_0(X3,k11_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_42])).

fof(c_0_46,plain,(
    ! [X13,X14] :
      ( ( r2_hidden(esk2_2(X13,X14),X13)
        | X13 = k1_tarski(X14)
        | X13 = k1_xboole_0 )
      & ( esk2_2(X13,X14) != X14
        | X13 = k1_tarski(X14)
        | X13 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk3_0,X1)
    | ~ r1_xboole_0(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_39])).

fof(c_0_48,plain,(
    ! [X20,X21] :
      ( ( k9_relat_1(X21,X20) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_xboole_0(k1_relat_1(X21),X20)
        | k9_relat_1(X21,X20) = k1_xboole_0
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_49,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,esk3_0),k11_relat_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_40]),c_0_41])])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ r1_xboole_0(k2_tarski(esk3_0,X1),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_21])).

cnf(c_0_53,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_54,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k2_tarski(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_49,c_0_14])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),X3)
    | ~ r2_hidden(k4_tarski(X4,X2),X3) ),
    inference(spm,[status(thm)],[c_0_36,c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk4_0,esk3_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_50]),c_0_41])])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X2,X2)
    | r2_hidden(esk2_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[c_0_51,c_0_14])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk4_0),k2_tarski(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,plain,
    ( r1_xboole_0(k1_relat_1(X1),k2_tarski(X2,X2))
    | k11_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk2_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk4_0,esk3_0) = X1
    | ~ r2_hidden(k4_tarski(esk3_0,X1),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_40]),c_0_41])])).

cnf(c_0_63,plain,
    ( k11_relat_1(X1,X2) = k2_tarski(X3,X3)
    | k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(k4_tarski(X2,esk2_2(k11_relat_1(X1,X2),X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_41])])).

cnf(c_0_65,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) != k1_tarski(k1_funct_1(esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X2,X2)
    | esk2_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_61,c_0_14])).

cnf(c_0_67,negated_conjecture,
    ( esk2_2(k11_relat_1(esk4_0,esk3_0),X1) = k1_funct_1(esk4_0,esk3_0)
    | k2_tarski(X1,X1) = k11_relat_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_41])]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( k11_relat_1(esk4_0,esk3_0) != k2_tarski(k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( k2_tarski(X1,X1) = k11_relat_1(esk4_0,esk3_0)
    | k1_funct_1(esk4_0,esk3_0) != X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_68,c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.19/0.50  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.028 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.50  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.50  fof(t12_zfmisc_1, axiom, ![X1, X2]:r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 0.19/0.50  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.19/0.50  fof(t204_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)<=>r2_hidden(X2,k11_relat_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 0.19/0.50  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.50  fof(t117_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 0.19/0.50  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.19/0.50  fof(l44_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 0.19/0.50  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.19/0.50  fof(c_0_10, plain, ![X11, X12]:((~r1_tarski(k1_tarski(X11),X12)|r2_hidden(X11,X12))&(~r2_hidden(X11,X12)|r1_tarski(k1_tarski(X11),X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.50  fof(c_0_11, plain, ![X10]:k2_tarski(X10,X10)=k1_tarski(X10), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.50  fof(c_0_12, plain, ![X16, X17]:r1_tarski(k1_tarski(X16),k2_tarski(X16,X17)), inference(variable_rename,[status(thm)],[t12_zfmisc_1])).
% 0.19/0.50  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.50  cnf(c_0_14, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.50  cnf(c_0_15, plain, (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.50  fof(c_0_16, plain, ![X4, X5, X7, X8, X9]:(((r2_hidden(esk1_2(X4,X5),X4)|r1_xboole_0(X4,X5))&(r2_hidden(esk1_2(X4,X5),X5)|r1_xboole_0(X4,X5)))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|~r1_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.19/0.50  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.50  cnf(c_0_18, plain, (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.19/0.50  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_21, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.50  cnf(c_0_22, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.50  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,k2_tarski(X1,X3))), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 0.19/0.50  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,X1)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.50  fof(c_0_25, plain, ![X22, X23, X24]:((~r2_hidden(k4_tarski(X22,X23),X24)|r2_hidden(X23,k11_relat_1(X24,X22))|~v1_relat_1(X24))&(~r2_hidden(X23,k11_relat_1(X24,X22))|r2_hidden(k4_tarski(X22,X23),X24)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).
% 0.19/0.50  fof(c_0_26, plain, ![X25, X26, X27]:(((r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(X26=k1_funct_1(X27,X25)|~r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27))))&(~r2_hidden(X25,k1_relat_1(X27))|X26!=k1_funct_1(X27,X25)|r2_hidden(k4_tarski(X25,X26),X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.50  cnf(c_0_27, plain, (~r2_hidden(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.50  cnf(c_0_28, plain, (r2_hidden(X2,k11_relat_1(X3,X1))|~r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  fof(c_0_30, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t117_funct_1])).
% 0.19/0.50  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X3,X1),X2)|~r2_hidden(X1,k11_relat_1(X2,X3))|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_33, plain, (~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,X3),X1)|~r1_xboole_0(k11_relat_1(X1,X2),k11_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.50  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_29])).
% 0.19/0.50  fof(c_0_35, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r2_hidden(esk3_0,k1_relat_1(esk4_0))&k11_relat_1(esk4_0,esk3_0)!=k1_tarski(k1_funct_1(esk4_0,esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])).
% 0.19/0.50  cnf(c_0_36, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  cnf(c_0_37, plain, (r2_hidden(k4_tarski(X1,esk1_2(X2,k11_relat_1(X3,X1))),X3)|r1_xboole_0(X2,k11_relat_1(X3,X1))|~v1_relat_1(X3)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.50  cnf(c_0_38, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_xboole_0(k11_relat_1(X1,X2),k11_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.50  cnf(c_0_39, negated_conjecture, (r2_hidden(esk3_0,k1_relat_1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.50  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.50  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.50  cnf(c_0_42, plain, (esk1_2(X1,k11_relat_1(X2,X3))=k1_funct_1(X2,X3)|r1_xboole_0(X1,k11_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.50  fof(c_0_43, plain, ![X18, X19]:(~v1_relat_1(X18)|k11_relat_1(X18,X19)=k9_relat_1(X18,k1_tarski(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.19/0.50  cnf(c_0_44, negated_conjecture, (~r1_xboole_0(k11_relat_1(esk4_0,esk3_0),k11_relat_1(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 0.19/0.50  cnf(c_0_45, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|r1_xboole_0(X3,k11_relat_1(X1,X2))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_42])).
% 0.19/0.50  fof(c_0_46, plain, ![X13, X14]:((r2_hidden(esk2_2(X13,X14),X13)|(X13=k1_tarski(X14)|X13=k1_xboole_0))&(esk2_2(X13,X14)!=X14|(X13=k1_tarski(X14)|X13=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l44_zfmisc_1])])])])).
% 0.19/0.50  cnf(c_0_47, negated_conjecture, (~r2_hidden(esk3_0,X1)|~r1_xboole_0(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_39])).
% 0.19/0.50  fof(c_0_48, plain, ![X20, X21]:((k9_relat_1(X21,X20)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_xboole_0(k1_relat_1(X21),X20)|k9_relat_1(X21,X20)=k1_xboole_0|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 0.19/0.50  cnf(c_0_49, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.50  cnf(c_0_50, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,esk3_0),k11_relat_1(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_40]), c_0_41])])).
% 0.19/0.50  cnf(c_0_51, plain, (r2_hidden(esk2_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.50  cnf(c_0_52, negated_conjecture, (~r1_xboole_0(k2_tarski(esk3_0,X1),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_21])).
% 0.19/0.50  cnf(c_0_53, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_32])).
% 0.19/0.50  cnf(c_0_54, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.50  cnf(c_0_55, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k2_tarski(X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_49, c_0_14])).
% 0.19/0.50  cnf(c_0_56, plain, (X1=X2|~v1_funct_1(X3)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),X3)|~r2_hidden(k4_tarski(X4,X2),X3)), inference(spm,[status(thm)],[c_0_36, c_0_36])).
% 0.19/0.50  cnf(c_0_57, negated_conjecture, (r2_hidden(k4_tarski(esk3_0,k1_funct_1(esk4_0,esk3_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_50]), c_0_41])])).
% 0.19/0.50  cnf(c_0_58, plain, (X1=k1_xboole_0|X1=k2_tarski(X2,X2)|r2_hidden(esk2_2(X1,X2),X1)), inference(rw,[status(thm)],[c_0_51, c_0_14])).
% 0.19/0.50  cnf(c_0_59, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk4_0),k2_tarski(esk3_0,X1))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.50  cnf(c_0_60, plain, (r1_xboole_0(k1_relat_1(X1),k2_tarski(X2,X2))|k11_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.50  cnf(c_0_61, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk2_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.50  cnf(c_0_62, negated_conjecture, (k1_funct_1(esk4_0,esk3_0)=X1|~r2_hidden(k4_tarski(esk3_0,X1),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_40]), c_0_41])])).
% 0.19/0.50  cnf(c_0_63, plain, (k11_relat_1(X1,X2)=k2_tarski(X3,X3)|k11_relat_1(X1,X2)=k1_xboole_0|r2_hidden(k4_tarski(X2,esk2_2(k11_relat_1(X1,X2),X3)),X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_58])).
% 0.19/0.50  cnf(c_0_64, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_41])])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)!=k1_tarski(k1_funct_1(esk4_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.50  cnf(c_0_66, plain, (X1=k1_xboole_0|X1=k2_tarski(X2,X2)|esk2_2(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_61, c_0_14])).
% 0.19/0.50  cnf(c_0_67, negated_conjecture, (esk2_2(k11_relat_1(esk4_0,esk3_0),X1)=k1_funct_1(esk4_0,esk3_0)|k2_tarski(X1,X1)=k11_relat_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_41])]), c_0_64])).
% 0.19/0.50  cnf(c_0_68, negated_conjecture, (k11_relat_1(esk4_0,esk3_0)!=k2_tarski(k1_funct_1(esk4_0,esk3_0),k1_funct_1(esk4_0,esk3_0))), inference(rw,[status(thm)],[c_0_65, c_0_14])).
% 0.19/0.50  cnf(c_0_69, negated_conjecture, (k2_tarski(X1,X1)=k11_relat_1(esk4_0,esk3_0)|k1_funct_1(esk4_0,esk3_0)!=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_64])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_68, c_0_69]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 71
% 0.19/0.50  # Proof object clause steps            : 50
% 0.19/0.50  # Proof object formula steps           : 21
% 0.19/0.50  # Proof object conjectures             : 19
% 0.19/0.50  # Proof object clause conjectures      : 16
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 18
% 0.19/0.50  # Proof object initial formulas used   : 10
% 0.19/0.50  # Proof object generating inferences   : 26
% 0.19/0.50  # Proof object simplifying inferences  : 23
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 10
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 21
% 0.19/0.50  # Removed in clause preprocessing      : 1
% 0.19/0.50  # Initial clauses in saturation        : 20
% 0.19/0.50  # Processed clauses                    : 876
% 0.19/0.50  # ...of these trivial                  : 1
% 0.19/0.50  # ...subsumed                          : 544
% 0.19/0.50  # ...remaining for further processing  : 331
% 0.19/0.50  # Other redundant clauses eliminated   : 46
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 9
% 0.19/0.50  # Backward-rewritten                   : 0
% 0.19/0.50  # Generated clauses                    : 5114
% 0.19/0.50  # ...of the previous two non-trivial   : 4784
% 0.19/0.50  # Contextual simplify-reflections      : 8
% 0.19/0.50  # Paramodulations                      : 5041
% 0.19/0.50  # Factorizations                       : 11
% 0.19/0.50  # Equation resolutions                 : 57
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 300
% 0.19/0.50  #    Positive orientable unit clauses  : 7
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 10
% 0.19/0.50  #    Non-unit-clauses                  : 283
% 0.19/0.50  # Current number of unprocessed clauses: 3938
% 0.19/0.50  # ...number of literals in the above   : 24458
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 30
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 17324
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 6640
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 425
% 0.19/0.50  # Unit Clause-clause subsumption calls : 65
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 0
% 0.19/0.50  # BW rewrite match successes           : 0
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 91305
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.156 s
% 0.19/0.50  # System time              : 0.008 s
% 0.19/0.50  # Total time               : 0.164 s
% 0.19/0.50  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
