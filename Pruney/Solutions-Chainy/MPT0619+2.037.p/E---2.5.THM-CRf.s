%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:55 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 640 expanded)
%              Number of clauses        :   50 ( 299 expanded)
%              Number of leaves         :    7 ( 151 expanded)
%              Depth                    :   17
%              Number of atoms          :  187 (1972 expanded)
%              Number of equality atoms :   98 (1061 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

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

fof(l22_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t41_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_tarski(X2)
        & X1 != k1_xboole_0
        & ! [X3] :
            ~ ( r2_hidden(X3,X1)
              & X3 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(c_0_7,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X7
        | X8 != k1_tarski(X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k1_tarski(X7) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | esk2_2(X11,X12) != X11
        | X12 = k1_tarski(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | esk2_2(X11,X12) = X11
        | X12 = k1_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_10,plain,(
    ! [X23,X24,X25,X27,X28,X29,X31] :
      ( ( r2_hidden(esk4_3(X23,X24,X25),k1_relat_1(X23))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X25 = k1_funct_1(X23,esk4_3(X23,X24,X25))
        | ~ r2_hidden(X25,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X28,k1_relat_1(X23))
        | X27 != k1_funct_1(X23,X28)
        | r2_hidden(X27,X24)
        | X24 != k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(esk5_2(X23,X29),X29)
        | ~ r2_hidden(X31,k1_relat_1(X23))
        | esk5_2(X23,X29) != k1_funct_1(X23,X31)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk6_2(X23,X29),k1_relat_1(X23))
        | r2_hidden(esk5_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( esk5_2(X23,X29) = k1_funct_1(X23,esk6_2(X23,X29))
        | r2_hidden(esk5_2(X23,X29),X29)
        | X29 = k2_relat_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & k1_relat_1(esk8_0) = k1_tarski(esk7_0)
    & k2_relat_1(esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_tarski(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | k2_xboole_0(k1_tarski(X15),X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).

cnf(c_0_18,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).

cnf(c_0_22,negated_conjecture,
    ( k1_relat_1(esk8_0) = k2_tarski(esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_12])).

fof(c_0_23,plain,(
    ! [X20,X21] : k2_xboole_0(k1_tarski(X20),X21) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_24,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk8_0))
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_28,plain,(
    ! [X17,X18] :
      ( ( r2_hidden(esk3_2(X17,X18),X17)
        | X17 = k1_tarski(X18)
        | X17 = k1_xboole_0 )
      & ( esk3_2(X17,X18) != X18
        | X17 = k1_tarski(X18)
        | X17 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).

cnf(c_0_29,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) = X2
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_24,c_0_12])).

cnf(c_0_31,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk7_0),k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_12])).

cnf(c_0_34,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | X1 = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_36,plain,
    ( k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_21])).

cnf(c_0_37,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k2_xboole_0(k2_tarski(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0)) = k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(esk8_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X2,X2)
    | r2_hidden(esk3_2(X1,X2),X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_12])).

cnf(c_0_42,plain,
    ( k2_tarski(X1,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( X1 = k1_tarski(X2)
    | X1 = k1_xboole_0
    | esk3_2(X1,X2) != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),X1)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_20])])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(esk8_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(esk8_0) != k2_tarski(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_12])).

cnf(c_0_47,plain,
    ( k2_tarski(X1,X1) = k2_tarski(X2,X2)
    | esk3_2(k2_tarski(X1,X1),X2) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_tarski(X2,X2)
    | esk3_2(X1,X2) != X2 ),
    inference(rw,[status(thm)],[c_0_43,c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1))) = esk3_2(k2_relat_1(esk8_0),X1)
    | k2_tarski(X1,X1) = k2_relat_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_41]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( esk3_2(k2_tarski(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)),X1) = k1_funct_1(esk8_0,esk7_0)
    | k2_tarski(X1,X1) != k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1))) = esk3_2(k2_relat_1(esk8_0),X1)
    | X2 = k2_relat_1(esk8_0)
    | X2 = k1_xboole_0
    | esk3_2(X2,X1) != X1 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1))) = esk3_2(k2_relat_1(esk8_0),X1)
    | esk3_2(k2_tarski(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)),X1) = k1_funct_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_54,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)))) = esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_46]),c_0_42])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),X1),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_19]),c_0_20])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0))
    | ~ r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_55]),c_0_19]),c_0_20])])).

cnf(c_0_58,negated_conjecture,
    ( k2_tarski(X1,X1) = k2_relat_1(esk8_0)
    | r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)),k1_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_45])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_46])).

cnf(c_0_60,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)) = k1_funct_1(esk8_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_63]),c_0_46]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:30:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S053I
% 0.46/0.66  # and selection function HSelectMinInfpos.
% 0.46/0.66  #
% 0.46/0.66  # Preprocessing time       : 0.028 s
% 0.46/0.66  # Presaturation interreduction done
% 0.46/0.66  
% 0.46/0.66  # Proof found!
% 0.46/0.66  # SZS status Theorem
% 0.46/0.66  # SZS output start CNFRefutation
% 0.46/0.66  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.46/0.66  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.46/0.66  fof(t14_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.46/0.66  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.46/0.66  fof(l22_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>k2_xboole_0(k1_tarski(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 0.46/0.66  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.46/0.66  fof(t41_zfmisc_1, axiom, ![X1, X2]:~(((X1!=k1_tarski(X2)&X1!=k1_xboole_0)&![X3]:~((r2_hidden(X3,X1)&X3!=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 0.46/0.66  fof(c_0_7, plain, ![X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X9,X8)|X9=X7|X8!=k1_tarski(X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k1_tarski(X7)))&((~r2_hidden(esk2_2(X11,X12),X12)|esk2_2(X11,X12)!=X11|X12=k1_tarski(X11))&(r2_hidden(esk2_2(X11,X12),X12)|esk2_2(X11,X12)=X11|X12=k1_tarski(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.46/0.66  fof(c_0_8, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.46/0.66  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t14_funct_1])).
% 0.46/0.66  fof(c_0_10, plain, ![X23, X24, X25, X27, X28, X29, X31]:((((r2_hidden(esk4_3(X23,X24,X25),k1_relat_1(X23))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X25=k1_funct_1(X23,esk4_3(X23,X24,X25))|~r2_hidden(X25,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X28,k1_relat_1(X23))|X27!=k1_funct_1(X23,X28)|r2_hidden(X27,X24)|X24!=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&((~r2_hidden(esk5_2(X23,X29),X29)|(~r2_hidden(X31,k1_relat_1(X23))|esk5_2(X23,X29)!=k1_funct_1(X23,X31))|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&((r2_hidden(esk6_2(X23,X29),k1_relat_1(X23))|r2_hidden(esk5_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(esk5_2(X23,X29)=k1_funct_1(X23,esk6_2(X23,X29))|r2_hidden(esk5_2(X23,X29),X29)|X29=k2_relat_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.46/0.66  cnf(c_0_11, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.66  cnf(c_0_12, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&(k1_relat_1(esk8_0)=k1_tarski(esk7_0)&k2_relat_1(esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.46/0.66  cnf(c_0_14, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.46/0.66  cnf(c_0_15, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.46/0.66  cnf(c_0_16, negated_conjecture, (k1_relat_1(esk8_0)=k1_tarski(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.46/0.66  fof(c_0_17, plain, ![X15, X16]:(~r2_hidden(X15,X16)|k2_xboole_0(k1_tarski(X15),X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_zfmisc_1])])).
% 0.46/0.66  cnf(c_0_18, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_14])])).
% 0.46/0.66  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.46/0.66  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.46/0.66  cnf(c_0_21, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_15])])).
% 0.46/0.66  cnf(c_0_22, negated_conjecture, (k1_relat_1(esk8_0)=k2_tarski(esk7_0,esk7_0)), inference(rw,[status(thm)],[c_0_16, c_0_12])).
% 0.46/0.66  fof(c_0_23, plain, ![X20, X21]:k2_xboole_0(k1_tarski(X20),X21)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.46/0.66  cnf(c_0_24, plain, (k2_xboole_0(k1_tarski(X1),X2)=X2|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.46/0.66  cnf(c_0_25, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,X1),k2_relat_1(esk8_0))|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.46/0.66  cnf(c_0_26, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.46/0.66  cnf(c_0_27, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.66  fof(c_0_28, plain, ![X17, X18]:((r2_hidden(esk3_2(X17,X18),X17)|(X17=k1_tarski(X18)|X17=k1_xboole_0))&(esk3_2(X17,X18)!=X18|(X17=k1_tarski(X18)|X17=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_zfmisc_1])])])])).
% 0.46/0.66  cnf(c_0_29, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.46/0.66  cnf(c_0_30, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)=X2|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_24, c_0_12])).
% 0.46/0.66  cnf(c_0_31, plain, (X1=k1_funct_1(X2,esk4_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.46/0.66  cnf(c_0_32, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,esk7_0),k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.46/0.66  cnf(c_0_33, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_27, c_0_12])).
% 0.46/0.66  cnf(c_0_34, plain, (r2_hidden(esk3_2(X1,X2),X1)|X1=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.66  cnf(c_0_35, plain, (k2_xboole_0(k2_tarski(X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_29, c_0_12])).
% 0.46/0.66  cnf(c_0_36, plain, (k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_30, c_0_21])).
% 0.46/0.66  cnf(c_0_37, plain, (k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_31])).
% 0.46/0.66  cnf(c_0_38, negated_conjecture, (k2_xboole_0(k2_tarski(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0))=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_32])).
% 0.46/0.66  cnf(c_0_39, negated_conjecture, (k2_relat_1(esk8_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.46/0.66  cnf(c_0_40, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_33])).
% 0.46/0.66  cnf(c_0_41, plain, (X1=k1_xboole_0|X1=k2_tarski(X2,X2)|r2_hidden(esk3_2(X1,X2),X1)), inference(rw,[status(thm)],[c_0_34, c_0_12])).
% 0.46/0.66  cnf(c_0_42, plain, (k2_tarski(X1,X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.46/0.66  cnf(c_0_43, plain, (X1=k1_tarski(X2)|X1=k1_xboole_0|esk3_2(X1,X2)!=X2), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.46/0.66  cnf(c_0_44, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),X1))=X1|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_20])])).
% 0.46/0.66  cnf(c_0_45, negated_conjecture, (k2_relat_1(esk8_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_38])).
% 0.46/0.66  cnf(c_0_46, negated_conjecture, (k2_relat_1(esk8_0)!=k2_tarski(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0))), inference(rw,[status(thm)],[c_0_39, c_0_12])).
% 0.46/0.66  cnf(c_0_47, plain, (k2_tarski(X1,X1)=k2_tarski(X2,X2)|esk3_2(k2_tarski(X1,X1),X2)=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.46/0.66  cnf(c_0_48, plain, (X1=k1_xboole_0|X1=k2_tarski(X2,X2)|esk3_2(X1,X2)!=X2), inference(rw,[status(thm)],[c_0_43, c_0_12])).
% 0.46/0.66  cnf(c_0_49, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)))=esk3_2(k2_relat_1(esk8_0),X1)|k2_tarski(X1,X1)=k2_relat_1(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_41]), c_0_45])).
% 0.46/0.66  cnf(c_0_50, negated_conjecture, (esk3_2(k2_tarski(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)),X1)=k1_funct_1(esk8_0,esk7_0)|k2_tarski(X1,X1)!=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.46/0.66  cnf(c_0_51, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.46/0.66  cnf(c_0_52, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)))=esk3_2(k2_relat_1(esk8_0),X1)|X2=k2_relat_1(esk8_0)|X2=k1_xboole_0|esk3_2(X2,X1)!=X1), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.46/0.66  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)))=esk3_2(k2_relat_1(esk8_0),X1)|esk3_2(k2_tarski(k1_funct_1(esk8_0,esk7_0),k1_funct_1(esk8_0,esk7_0)),X1)=k1_funct_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.46/0.66  cnf(c_0_54, plain, (r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_51])).
% 0.46/0.66  cnf(c_0_55, negated_conjecture, (k1_funct_1(esk8_0,esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))))=esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_46]), c_0_42])])).
% 0.46/0.66  cnf(c_0_56, negated_conjecture, (r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),X1),k1_relat_1(esk8_0))|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_19]), c_0_20])])).
% 0.46/0.66  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0))|~r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))),k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_55]), c_0_19]), c_0_20])])).
% 0.46/0.66  cnf(c_0_58, negated_conjecture, (k2_tarski(X1,X1)=k2_relat_1(esk8_0)|r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),X1)),k1_relat_1(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_41]), c_0_45])).
% 0.46/0.66  cnf(c_0_59, negated_conjecture, (r2_hidden(esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)),k2_relat_1(esk8_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_46])).
% 0.46/0.66  cnf(c_0_60, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_40, c_0_22])).
% 0.46/0.66  cnf(c_0_61, negated_conjecture, (r2_hidden(esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))),k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_56, c_0_59])).
% 0.46/0.66  cnf(c_0_62, negated_conjecture, (esk4_3(esk8_0,k2_relat_1(esk8_0),esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0)))=esk7_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.46/0.66  cnf(c_0_63, negated_conjecture, (esk3_2(k2_relat_1(esk8_0),k1_funct_1(esk8_0,esk7_0))=k1_funct_1(esk8_0,esk7_0)), inference(rw,[status(thm)],[c_0_55, c_0_62])).
% 0.46/0.66  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_63]), c_0_46]), c_0_45]), ['proof']).
% 0.46/0.66  # SZS output end CNFRefutation
% 0.46/0.66  # Proof object total steps             : 65
% 0.46/0.66  # Proof object clause steps            : 50
% 0.46/0.66  # Proof object formula steps           : 15
% 0.46/0.66  # Proof object conjectures             : 29
% 0.46/0.66  # Proof object clause conjectures      : 26
% 0.46/0.66  # Proof object formula conjectures     : 3
% 0.46/0.66  # Proof object initial clauses used    : 14
% 0.46/0.66  # Proof object initial formulas used   : 7
% 0.46/0.66  # Proof object generating inferences   : 22
% 0.46/0.66  # Proof object simplifying inferences  : 34
% 0.46/0.66  # Training examples: 0 positive, 0 negative
% 0.46/0.66  # Parsed axioms                        : 9
% 0.46/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.66  # Initial clauses                      : 22
% 0.46/0.66  # Removed in clause preprocessing      : 1
% 0.46/0.66  # Initial clauses in saturation        : 21
% 0.46/0.66  # Processed clauses                    : 1020
% 0.46/0.66  # ...of these trivial                  : 3
% 0.46/0.66  # ...subsumed                          : 624
% 0.46/0.66  # ...remaining for further processing  : 393
% 0.46/0.66  # Other redundant clauses eliminated   : 1142
% 0.46/0.66  # Clauses deleted for lack of memory   : 0
% 0.46/0.66  # Backward-subsumed                    : 14
% 0.46/0.66  # Backward-rewritten                   : 14
% 0.46/0.66  # Generated clauses                    : 19968
% 0.46/0.66  # ...of the previous two non-trivial   : 17822
% 0.46/0.66  # Contextual simplify-reflections      : 6
% 0.46/0.66  # Paramodulations                      : 18656
% 0.46/0.66  # Factorizations                       : 166
% 0.46/0.66  # Equation resolutions                 : 1146
% 0.46/0.66  # Propositional unsat checks           : 0
% 0.46/0.66  #    Propositional check models        : 0
% 0.46/0.66  #    Propositional check unsatisfiable : 0
% 0.46/0.66  #    Propositional clauses             : 0
% 0.46/0.66  #    Propositional clauses after purity: 0
% 0.46/0.66  #    Propositional unsat core size     : 0
% 0.46/0.66  #    Propositional preprocessing time  : 0.000
% 0.46/0.66  #    Propositional encoding time       : 0.000
% 0.46/0.66  #    Propositional solver time         : 0.000
% 0.46/0.66  #    Success case prop preproc time    : 0.000
% 0.46/0.66  #    Success case prop encoding time   : 0.000
% 0.46/0.66  #    Success case prop solver time     : 0.000
% 0.46/0.66  # Current number of processed clauses  : 337
% 0.46/0.66  #    Positive orientable unit clauses  : 17
% 0.46/0.66  #    Positive unorientable unit clauses: 0
% 0.46/0.66  #    Negative unit clauses             : 7
% 0.46/0.66  #    Non-unit-clauses                  : 313
% 0.46/0.66  # Current number of unprocessed clauses: 16748
% 0.46/0.66  # ...number of literals in the above   : 80453
% 0.46/0.66  # Current number of archived formulas  : 0
% 0.46/0.66  # Current number of archived clauses   : 52
% 0.46/0.66  # Clause-clause subsumption calls (NU) : 20001
% 0.46/0.66  # Rec. Clause-clause subsumption calls : 8848
% 0.46/0.66  # Non-unit clause-clause subsumptions  : 586
% 0.46/0.66  # Unit Clause-clause subsumption calls : 377
% 0.46/0.66  # Rewrite failures with RHS unbound    : 0
% 0.46/0.66  # BW rewrite match attempts            : 55
% 0.46/0.66  # BW rewrite match successes           : 9
% 0.46/0.66  # Condensation attempts                : 0
% 0.46/0.66  # Condensation successes               : 0
% 0.46/0.66  # Termbank termtop insertions          : 317770
% 0.46/0.66  
% 0.46/0.66  # -------------------------------------------------
% 0.46/0.66  # User time                : 0.312 s
% 0.46/0.66  # System time              : 0.010 s
% 0.46/0.66  # Total time               : 0.322 s
% 0.46/0.66  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
