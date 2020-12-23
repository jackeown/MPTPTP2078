%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:11 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 925 expanded)
%              Number of clauses        :   51 ( 409 expanded)
%              Number of leaves         :    9 ( 250 expanded)
%              Depth                    :   21
%              Number of atoms          :  207 (3393 expanded)
%              Number of equality atoms :  113 (1721 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(t15_funct_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(c_0_9,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X15
        | X16 != k1_tarski(X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_tarski(X15) )
      & ( ~ r2_hidden(esk3_2(X19,X20),X20)
        | esk3_2(X19,X20) != X19
        | X20 = k1_tarski(X19) )
      & ( r2_hidden(esk3_2(X19,X20),X20)
        | esk3_2(X19,X20) = X19
        | X20 = k1_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

cnf(c_0_11,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X22] :
      ( ( k1_relat_1(X22) != k1_xboole_0
        | X22 = k1_xboole_0
        | ~ v1_relat_1(X22) )
      & ( k2_relat_1(X22) != k1_xboole_0
        | X22 = k1_xboole_0
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_14,plain,(
    ! [X24,X25,X27] :
      ( v1_relat_1(esk4_2(X24,X25))
      & v1_funct_1(esk4_2(X24,X25))
      & k1_relat_1(esk4_2(X24,X25)) = X24
      & ( ~ r2_hidden(X27,X24)
        | k1_funct_1(esk4_2(X24,X25),X27) = X25 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_15,negated_conjecture,(
    ! [X33] :
      ( ( esk6_0 != k1_xboole_0
        | esk7_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | esk7_0 != k1_relat_1(X33)
        | ~ r1_tarski(k2_relat_1(X33),esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_16,plain,(
    ! [X28,X29] :
      ( ( v1_relat_1(esk5_2(X28,X29))
        | X28 = k1_xboole_0 )
      & ( v1_funct_1(esk5_2(X28,X29))
        | X28 = k1_xboole_0 )
      & ( k1_relat_1(esk5_2(X28,X29)) = X28
        | X28 = k1_xboole_0 )
      & ( k2_relat_1(esk5_2(X28,X29)) = k1_tarski(X29)
        | X28 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( k1_relat_1(esk4_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_relat_1(esk4_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk7_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( v1_funct_1(esk5_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk5_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( esk1_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_27,plain,(
    ! [X23] :
      ( ( k1_relat_1(X23) != k1_xboole_0
        | k2_relat_1(X23) = k1_xboole_0
        | ~ v1_relat_1(X23) )
      & ( k2_relat_1(X23) != k1_xboole_0
        | k1_relat_1(X23) = k1_xboole_0
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_28,plain,
    ( esk4_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk5_2(X1,X2)) != esk7_0
    | ~ r1_tarski(k2_relat_1(esk5_2(X1,X2)),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_30,plain,
    ( k2_relat_1(esk5_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( v1_funct_1(esk4_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_28])).

cnf(c_0_35,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

fof(c_0_36,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_37,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk5_2(X1,X2)) != esk7_0
    | ~ r1_tarski(k1_tarski(X2),esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_tarski(esk1_2(X1,X2)),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_18])).

cnf(c_0_39,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_40,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k1_xboole_0
    | r1_tarski(esk6_0,X2)
    | k1_relat_1(esk5_2(X1,esk1_2(esk6_0,X2))) != esk7_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_39]),c_0_35])]),c_0_34]),c_0_40]),c_0_41])])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43])]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( esk3_2(X1,esk6_0) = X1
    | k1_tarski(X1) = esk6_0
    | r2_hidden(esk3_2(X1,esk6_0),X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_50,negated_conjecture,
    ( esk3_2(X1,esk6_0) = X1
    | esk3_2(X1,esk6_0) = X2
    | k1_tarski(X1) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_49])).

cnf(c_0_51,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_52,negated_conjecture,
    ( esk3_2(X1,esk6_0) = X1
    | k1_tarski(X1) = esk6_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_50])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k1_tarski(X1) = esk6_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_55,plain,
    ( esk3_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0
    | r2_hidden(esk3_2(X1,k1_xboole_0),X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_48])).

fof(c_0_56,plain,(
    ! [X11,X12] :
      ( ( ~ r2_hidden(esk2_2(X11,X12),X11)
        | ~ r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 )
      & ( r2_hidden(esk2_2(X11,X12),X11)
        | r2_hidden(esk2_2(X11,X12),X12)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_57,negated_conjecture,
    ( k1_tarski(esk3_2(X1,k1_xboole_0)) = esk6_0
    | esk3_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r2_hidden(esk2_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( esk3_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_relat_1(esk5_2(X2,esk3_2(X1,k1_xboole_0))) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_57]),c_0_46])])).

cnf(c_0_60,negated_conjecture,
    ( k1_tarski(esk2_2(esk6_0,X1)) = esk6_0
    | esk6_0 = X1
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( esk3_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_43])]),c_0_44])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = X1
    | X2 = k1_xboole_0
    | r2_hidden(esk2_2(esk6_0,X1),X1)
    | k1_relat_1(esk5_2(X2,esk2_2(esk6_0,X1))) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_60]),c_0_46])])).

cnf(c_0_63,negated_conjecture,
    ( k1_tarski(X1) = k1_xboole_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( esk6_0 = X1
    | r2_hidden(esk2_2(esk6_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_43])]),c_0_44])).

cnf(c_0_65,negated_conjecture,
    ( k1_tarski(esk2_2(esk6_0,k1_xboole_0)) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_66,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_relat_1(esk5_2(X1,esk2_2(esk6_0,k1_xboole_0))) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_65]),c_0_41])])).

cnf(c_0_67,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_68,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_43])]),c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:48:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.12/0.37  # and selection function SelectCQIPrecW.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.12/0.37  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.12/0.37  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.12/0.37  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 0.12/0.37  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.12/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.37  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 0.12/0.37  fof(c_0_9, plain, ![X15, X16, X17, X18, X19, X20]:(((~r2_hidden(X17,X16)|X17=X15|X16!=k1_tarski(X15))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_tarski(X15)))&((~r2_hidden(esk3_2(X19,X20),X20)|esk3_2(X19,X20)!=X19|X20=k1_tarski(X19))&(r2_hidden(esk3_2(X19,X20),X20)|esk3_2(X19,X20)=X19|X20=k1_tarski(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.12/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.12/0.37  cnf(c_0_11, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  fof(c_0_12, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  fof(c_0_13, plain, ![X22]:((k1_relat_1(X22)!=k1_xboole_0|X22=k1_xboole_0|~v1_relat_1(X22))&(k2_relat_1(X22)!=k1_xboole_0|X22=k1_xboole_0|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.12/0.37  fof(c_0_14, plain, ![X24, X25, X27]:(((v1_relat_1(esk4_2(X24,X25))&v1_funct_1(esk4_2(X24,X25)))&k1_relat_1(esk4_2(X24,X25))=X24)&(~r2_hidden(X27,X24)|k1_funct_1(esk4_2(X24,X25),X27)=X25)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.12/0.37  fof(c_0_15, negated_conjecture, ![X33]:((esk6_0!=k1_xboole_0|esk7_0=k1_xboole_0)&(~v1_relat_1(X33)|~v1_funct_1(X33)|(esk7_0!=k1_relat_1(X33)|~r1_tarski(k2_relat_1(X33),esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.12/0.37  fof(c_0_16, plain, ![X28, X29]:((((v1_relat_1(esk5_2(X28,X29))|X28=k1_xboole_0)&(v1_funct_1(esk5_2(X28,X29))|X28=k1_xboole_0))&(k1_relat_1(esk5_2(X28,X29))=X28|X28=k1_xboole_0))&(k2_relat_1(esk5_2(X28,X29))=k1_tarski(X29)|X28=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.12/0.37  cnf(c_0_17, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_19, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_20, plain, (k1_relat_1(esk4_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_21, plain, (v1_relat_1(esk4_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk7_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_23, plain, (v1_funct_1(esk5_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_24, plain, (v1_relat_1(esk5_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_26, plain, (esk1_2(k1_tarski(X1),X2)=X1|r1_tarski(k1_tarski(X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.12/0.37  fof(c_0_27, plain, ![X23]:((k1_relat_1(X23)!=k1_xboole_0|k2_relat_1(X23)=k1_xboole_0|~v1_relat_1(X23))&(k2_relat_1(X23)!=k1_xboole_0|k1_relat_1(X23)=k1_xboole_0|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.12/0.37  cnf(c_0_28, plain, (esk4_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk5_2(X1,X2))!=esk7_0|~r1_tarski(k2_relat_1(esk5_2(X1,X2)),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.12/0.37  cnf(c_0_30, plain, (k2_relat_1(esk5_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_31, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_32, plain, (v1_funct_1(esk4_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_33, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.37  cnf(c_0_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_28])).
% 0.12/0.37  cnf(c_0_35, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 0.12/0.37  fof(c_0_36, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk5_2(X1,X2))!=esk7_0|~r1_tarski(k1_tarski(X2),esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.12/0.37  cnf(c_0_38, plain, (r1_tarski(k1_tarski(esk1_2(X1,X2)),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_18])).
% 0.12/0.37  cnf(c_0_39, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 0.12/0.37  cnf(c_0_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.12/0.37  cnf(c_0_41, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (X1=k1_xboole_0|r1_tarski(esk6_0,X2)|k1_relat_1(esk5_2(X1,esk1_2(esk6_0,X2)))!=esk7_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_43, plain, (k1_relat_1(esk5_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_39]), c_0_35])]), c_0_34]), c_0_40]), c_0_41])])).
% 0.12/0.37  cnf(c_0_45, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (r1_tarski(esk6_0,X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43])]), c_0_44])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.37  cnf(c_0_48, plain, (r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (esk3_2(X1,esk6_0)=X1|k1_tarski(X1)=esk6_0|r2_hidden(esk3_2(X1,esk6_0),X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (esk3_2(X1,esk6_0)=X1|esk3_2(X1,esk6_0)=X2|k1_tarski(X1)=esk6_0), inference(spm,[status(thm)],[c_0_17, c_0_49])).
% 0.12/0.37  cnf(c_0_51, plain, (X2=k1_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (esk3_2(X1,esk6_0)=X1|k1_tarski(X1)=esk6_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_50])])).
% 0.12/0.37  cnf(c_0_53, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (k1_tarski(X1)=esk6_0|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.37  cnf(c_0_55, plain, (esk3_2(X1,k1_xboole_0)=X1|k1_tarski(X1)=k1_xboole_0|r2_hidden(esk3_2(X1,k1_xboole_0),X2)), inference(spm,[status(thm)],[c_0_53, c_0_48])).
% 0.12/0.37  fof(c_0_56, plain, ![X11, X12]:((~r2_hidden(esk2_2(X11,X12),X11)|~r2_hidden(esk2_2(X11,X12),X12)|X11=X12)&(r2_hidden(esk2_2(X11,X12),X11)|r2_hidden(esk2_2(X11,X12),X12)|X11=X12)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (k1_tarski(esk3_2(X1,k1_xboole_0))=esk6_0|esk3_2(X1,k1_xboole_0)=X1|k1_tarski(X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.12/0.37  cnf(c_0_58, plain, (r2_hidden(esk2_2(X1,X2),X1)|r2_hidden(esk2_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (esk3_2(X1,k1_xboole_0)=X1|k1_tarski(X1)=k1_xboole_0|X2=k1_xboole_0|k1_relat_1(esk5_2(X2,esk3_2(X1,k1_xboole_0)))!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_57]), c_0_46])])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (k1_tarski(esk2_2(esk6_0,X1))=esk6_0|esk6_0=X1|r2_hidden(esk2_2(esk6_0,X1),X1)), inference(spm,[status(thm)],[c_0_54, c_0_58])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (esk3_2(X1,k1_xboole_0)=X1|k1_tarski(X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_43])]), c_0_44])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (esk6_0=X1|X2=k1_xboole_0|r2_hidden(esk2_2(esk6_0,X1),X1)|k1_relat_1(esk5_2(X2,esk2_2(esk6_0,X1)))!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_60]), c_0_46])])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (k1_tarski(X1)=k1_xboole_0|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_61])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (esk6_0=X1|r2_hidden(esk2_2(esk6_0,X1),X1)), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_43])]), c_0_44])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (k1_tarski(esk2_2(esk6_0,k1_xboole_0))=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (esk6_0=k1_xboole_0|X1=k1_xboole_0|k1_relat_1(esk5_2(X1,esk2_2(esk6_0,k1_xboole_0)))!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_65]), c_0_41])])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (esk6_0=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_43])]), c_0_44])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])]), c_0_44]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 70
% 0.12/0.37  # Proof object clause steps            : 51
% 0.12/0.37  # Proof object formula steps           : 19
% 0.12/0.37  # Proof object conjectures             : 26
% 0.12/0.37  # Proof object clause conjectures      : 23
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 19
% 0.12/0.37  # Proof object initial formulas used   : 9
% 0.12/0.37  # Proof object generating inferences   : 30
% 0.12/0.37  # Proof object simplifying inferences  : 31
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 9
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 24
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 24
% 0.12/0.37  # Processed clauses                    : 104
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 9
% 0.12/0.37  # ...remaining for further processing  : 94
% 0.12/0.37  # Other redundant clauses eliminated   : 17
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 9
% 0.12/0.37  # Backward-rewritten                   : 16
% 0.12/0.37  # Generated clauses                    : 206
% 0.12/0.37  # ...of the previous two non-trivial   : 172
% 0.12/0.37  # Contextual simplify-reflections      : 3
% 0.12/0.37  # Paramodulations                      : 183
% 0.12/0.37  # Factorizations                       : 7
% 0.12/0.37  # Equation resolutions                 : 17
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 43
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 29
% 0.12/0.37  # Current number of unprocessed clauses: 73
% 0.12/0.37  # ...number of literals in the above   : 266
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 49
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 246
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 183
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 21
% 0.12/0.37  # Unit Clause-clause subsumption calls : 34
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 10
% 0.12/0.37  # BW rewrite match successes           : 3
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3596
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.033 s
% 0.18/0.37  # System time              : 0.004 s
% 0.18/0.37  # Total time               : 0.037 s
% 0.18/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
