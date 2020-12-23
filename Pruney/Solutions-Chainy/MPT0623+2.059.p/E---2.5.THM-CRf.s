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
% DateTime   : Thu Dec  3 10:53:13 EST 2020

% Result     : Theorem 29.79s
% Output     : CNFRefutation 29.79s
% Verified   : 
% Statistics : Number of formulae       :   75 (43910 expanded)
%              Number of clauses        :   63 (19078 expanded)
%              Number of leaves         :    6 (12988 expanded)
%              Depth                    :   24
%              Number of atoms          :  228 (165797 expanded)
%              Number of equality atoms :   67 (73418 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

fof(c_0_7,plain,(
    ! [X11] :
      ( ( k1_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) != k1_xboole_0
        | X11 = k1_xboole_0
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_8,plain,(
    ! [X22,X23,X25] :
      ( v1_relat_1(esk5_2(X22,X23))
      & v1_funct_1(esk5_2(X22,X23))
      & k1_relat_1(esk5_2(X22,X23)) = X22
      & ( ~ r2_hidden(X25,X22)
        | k1_funct_1(esk5_2(X22,X23),X25) = X23 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_9,negated_conjecture,(
    ! [X28] :
      ( ( esk6_0 != k1_xboole_0
        | esk7_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28)
        | esk7_0 != k1_relat_1(X28)
        | ~ r1_tarski(k2_relat_1(X28),esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk7_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_16,plain,(
    ! [X12,X13,X14,X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 = k1_funct_1(X12,esk2_3(X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | r2_hidden(X16,X13)
        | X13 != k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X12))
        | esk3_2(X12,X18) != k1_funct_1(X12,X20)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X18) = k1_funct_1(X12,esk4_2(X12,X18))
        | r2_hidden(esk3_2(X12,X18),X18)
        | X18 = k2_relat_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_17,plain,
    ( esk5_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_14]),c_0_12])])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_17])).

cnf(c_0_22,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_23,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_24,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0),k2_relat_1(esk5_2(esk7_0,X1))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_2(k1_xboole_0,X1),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24])])).

cnf(c_0_27,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | r2_hidden(esk4_2(k1_xboole_0,esk7_0),k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_17]),c_0_22]),c_0_17]),c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,esk7_0)) = X1
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_17])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_29])).

cnf(c_0_32,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | ~ r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_34,plain,
    ( r2_hidden(k1_funct_1(esk5_2(X1,X2),X3),k2_relat_1(esk5_2(X1,X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_14]),c_0_12]),c_0_11])])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X1)),X2),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)) = X2 ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X2)),X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk5_2(k2_relat_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X1)),X2)),X3),X2) = X3 ),
    inference(spm,[status(thm)],[c_0_27,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,X1) = X2
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_17]),c_0_22]),c_0_17]),c_0_22]),c_0_17])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,esk6_0)) = X1
    | r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_43]),c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | ~ r1_tarski(k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | ~ r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_46]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_52]),c_0_53])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,esk6_0)) = X1
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_57]),c_0_17])).

cnf(c_0_61,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_62,plain,
    ( r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_14]),c_0_11]),c_0_12])])).

cnf(c_0_63,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_60])).

cnf(c_0_64,plain,
    ( k1_funct_1(esk5_2(X1,X2),esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3)) = X3
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_14]),c_0_12])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | ~ r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0))) = esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_25])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X2),k2_relat_1(esk5_2(esk7_0,X2)),esk1_2(k2_relat_1(esk5_2(esk7_0,X2)),esk6_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_27,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) = X1 ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_69]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_71]),c_0_18])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_72,c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 29.79/29.98  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 29.79/29.98  # and selection function SelectCQIArEqFirst.
% 29.79/29.98  #
% 29.79/29.98  # Preprocessing time       : 0.027 s
% 29.79/29.98  # Presaturation interreduction done
% 29.79/29.98  
% 29.79/29.98  # Proof found!
% 29.79/29.98  # SZS status Theorem
% 29.79/29.98  # SZS output start CNFRefutation
% 29.79/29.98  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 29.79/29.98  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 29.79/29.98  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 29.79/29.98  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 29.79/29.98  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 29.79/29.98  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 29.79/29.98  fof(c_0_6, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 29.79/29.98  fof(c_0_7, plain, ![X11]:((k1_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))&(k2_relat_1(X11)!=k1_xboole_0|X11=k1_xboole_0|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 29.79/29.98  fof(c_0_8, plain, ![X22, X23, X25]:(((v1_relat_1(esk5_2(X22,X23))&v1_funct_1(esk5_2(X22,X23)))&k1_relat_1(esk5_2(X22,X23))=X22)&(~r2_hidden(X25,X22)|k1_funct_1(esk5_2(X22,X23),X25)=X23)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 29.79/29.98  fof(c_0_9, negated_conjecture, ![X28]:((esk6_0!=k1_xboole_0|esk7_0=k1_xboole_0)&(~v1_relat_1(X28)|~v1_funct_1(X28)|(esk7_0!=k1_relat_1(X28)|~r1_tarski(k2_relat_1(X28),esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 29.79/29.98  cnf(c_0_10, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 29.79/29.98  cnf(c_0_11, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 29.79/29.98  cnf(c_0_12, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 29.79/29.98  cnf(c_0_13, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk7_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 29.79/29.98  cnf(c_0_14, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 29.79/29.98  fof(c_0_15, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 29.79/29.98  fof(c_0_16, plain, ![X12, X13, X14, X16, X17, X18, X20]:((((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X12))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(X14=k1_funct_1(X12,esk2_3(X12,X13,X14))|~r2_hidden(X14,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(X17,k1_relat_1(X12))|X16!=k1_funct_1(X12,X17)|r2_hidden(X16,X13)|X13!=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((~r2_hidden(esk3_2(X12,X18),X18)|(~r2_hidden(X20,k1_relat_1(X12))|esk3_2(X12,X18)!=k1_funct_1(X12,X20))|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&((r2_hidden(esk4_2(X12,X18),k1_relat_1(X12))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(esk3_2(X12,X18)=k1_funct_1(X12,esk4_2(X12,X18))|r2_hidden(esk3_2(X12,X18),X18)|X18=k2_relat_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 29.79/29.98  cnf(c_0_17, plain, (esk5_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])])).
% 29.79/29.98  cnf(c_0_18, negated_conjecture, (~r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_11]), c_0_14]), c_0_12])])])).
% 29.79/29.98  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 29.79/29.98  cnf(c_0_20, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 29.79/29.98  cnf(c_0_21, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_14, c_0_17])).
% 29.79/29.98  cnf(c_0_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 29.79/29.98  cnf(c_0_23, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 29.79/29.98  cnf(c_0_24, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_12, c_0_17])).
% 29.79/29.98  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0),k2_relat_1(esk5_2(esk7_0,X1)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 29.79/29.98  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_hidden(esk4_2(k1_xboole_0,X1),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24])])).
% 29.79/29.98  cnf(c_0_27, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 29.79/29.98  cnf(c_0_28, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|r2_hidden(esk4_2(k1_xboole_0,esk7_0),k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_17]), c_0_22]), c_0_17]), c_0_22])).
% 29.79/29.98  cnf(c_0_29, negated_conjecture, (k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,esk7_0))=X1|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_17])).
% 29.79/29.98  cnf(c_0_30, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 29.79/29.98  cnf(c_0_31, negated_conjecture, (X1=X2|r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_29])).
% 29.79/29.98  cnf(c_0_32, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_30])])).
% 29.79/29.98  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|~r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),X2)), inference(spm,[status(thm)],[c_0_18, c_0_31])).
% 29.79/29.98  cnf(c_0_34, plain, (r2_hidden(k1_funct_1(esk5_2(X1,X2),X3),k2_relat_1(esk5_2(X1,X2)))|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_14]), c_0_12]), c_0_11])])).
% 29.79/29.98  cnf(c_0_35, negated_conjecture, (k1_funct_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X1)),X2),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0))=X2), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 29.79/29.98  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 29.79/29.98  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 29.79/29.98  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,k2_relat_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X2)),X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_25]), c_0_35])).
% 29.79/29.98  cnf(c_0_39, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 29.79/29.98  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_37])).
% 29.79/29.98  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk5_2(k2_relat_1(esk5_2(k2_relat_1(esk5_2(esk7_0,X1)),X2)),X3),X2)=X3), inference(spm,[status(thm)],[c_0_27, c_0_38])).
% 29.79/29.98  cnf(c_0_42, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_26])).
% 29.79/29.98  cnf(c_0_43, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_28])).
% 29.79/29.98  cnf(c_0_44, negated_conjecture, (k1_funct_1(k1_xboole_0,X1)=X2|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_17]), c_0_22]), c_0_17]), c_0_22]), c_0_17])).
% 29.79/29.98  cnf(c_0_45, negated_conjecture, (k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,esk6_0))=X1|r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_43]), c_0_17])).
% 29.79/29.98  cnf(c_0_46, negated_conjecture, (X1=X2|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_44, c_0_44])).
% 29.79/29.98  cnf(c_0_47, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|~r1_tarski(k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_18, c_0_45])).
% 29.79/29.98  cnf(c_0_48, negated_conjecture, (X1=X2|r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)), inference(spm,[status(thm)],[c_0_45, c_0_45])).
% 29.79/29.98  cnf(c_0_49, negated_conjecture, (r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|~r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),X2)), inference(spm,[status(thm)],[c_0_18, c_0_46])).
% 29.79/29.98  cnf(c_0_50, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 29.79/29.98  cnf(c_0_51, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_49, c_0_46])).
% 29.79/29.98  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_48])).
% 29.79/29.98  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 29.79/29.98  cnf(c_0_54, negated_conjecture, (r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_46]), c_0_51])).
% 29.79/29.98  cnf(c_0_55, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk7_0),esk7_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_52]), c_0_53])).
% 29.79/29.98  cnf(c_0_56, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 29.79/29.98  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 29.79/29.98  cnf(c_0_58, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 29.79/29.98  cnf(c_0_59, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_56])).
% 29.79/29.98  cnf(c_0_60, negated_conjecture, (k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,esk6_0))=X1|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_57]), c_0_17])).
% 29.79/29.98  cnf(c_0_61, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_58])).
% 29.79/29.98  cnf(c_0_62, plain, (r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_14]), c_0_11]), c_0_12])])).
% 29.79/29.98  cnf(c_0_63, negated_conjecture, (X1=X2|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_60, c_0_60])).
% 29.79/29.98  cnf(c_0_64, plain, (k1_funct_1(esk5_2(X1,X2),esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3))=X3|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_14]), c_0_12])])).
% 29.79/29.98  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_62, c_0_25])).
% 29.79/29.98  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|~r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),X2)), inference(spm,[status(thm)],[c_0_18, c_0_63])).
% 29.79/29.98  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)))=esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)), inference(spm,[status(thm)],[c_0_64, c_0_25])).
% 29.79/29.98  cnf(c_0_68, negated_conjecture, (k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X2),k2_relat_1(esk5_2(esk7_0,X2)),esk1_2(k2_relat_1(esk5_2(esk7_0,X2)),esk6_0)))=X1), inference(spm,[status(thm)],[c_0_27, c_0_65])).
% 29.79/29.98  cnf(c_0_69, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_63])).
% 29.79/29.98  cnf(c_0_70, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_66, c_0_63])).
% 29.79/29.98  cnf(c_0_71, negated_conjecture, (esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)=X1), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 29.79/29.98  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_69]), c_0_70])).
% 29.79/29.98  cnf(c_0_73, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_71]), c_0_18])).
% 29.79/29.98  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_72, c_0_73]), ['proof']).
% 29.79/29.98  # SZS output end CNFRefutation
% 29.79/29.98  # Proof object total steps             : 75
% 29.79/29.98  # Proof object clause steps            : 63
% 29.79/29.98  # Proof object formula steps           : 12
% 29.79/29.98  # Proof object conjectures             : 43
% 29.79/29.98  # Proof object clause conjectures      : 40
% 29.79/29.98  # Proof object formula conjectures     : 3
% 29.79/29.98  # Proof object initial clauses used    : 15
% 29.79/29.98  # Proof object initial formulas used   : 6
% 29.79/29.98  # Proof object generating inferences   : 43
% 29.79/29.98  # Proof object simplifying inferences  : 43
% 29.79/29.98  # Training examples: 0 positive, 0 negative
% 29.79/29.98  # Parsed axioms                        : 6
% 29.79/29.98  # Removed by relevancy pruning/SinE    : 0
% 29.79/29.98  # Initial clauses                      : 19
% 29.79/29.98  # Removed in clause preprocessing      : 0
% 29.79/29.98  # Initial clauses in saturation        : 19
% 29.79/29.98  # Processed clauses                    : 13769
% 29.79/29.98  # ...of these trivial                  : 54
% 29.79/29.98  # ...subsumed                          : 10791
% 29.79/29.98  # ...remaining for further processing  : 2924
% 29.79/29.98  # Other redundant clauses eliminated   : 31361
% 29.79/29.98  # Clauses deleted for lack of memory   : 604648
% 29.79/29.98  # Backward-subsumed                    : 983
% 29.79/29.98  # Backward-rewritten                   : 68
% 29.79/29.98  # Generated clauses                    : 2652700
% 29.79/29.98  # ...of the previous two non-trivial   : 2552941
% 29.79/29.98  # Contextual simplify-reflections      : 153
% 29.79/29.98  # Paramodulations                      : 2620927
% 29.79/29.98  # Factorizations                       : 176
% 29.79/29.98  # Equation resolutions                 : 31364
% 29.79/29.98  # Propositional unsat checks           : 0
% 29.79/29.98  #    Propositional check models        : 0
% 29.79/29.98  #    Propositional check unsatisfiable : 0
% 29.79/29.98  #    Propositional clauses             : 0
% 29.79/29.98  #    Propositional clauses after purity: 0
% 29.79/29.98  #    Propositional unsat core size     : 0
% 29.79/29.98  #    Propositional preprocessing time  : 0.000
% 29.79/29.98  #    Propositional encoding time       : 0.000
% 29.79/29.98  #    Propositional solver time         : 0.000
% 29.79/29.98  #    Success case prop preproc time    : 0.000
% 29.79/29.98  #    Success case prop encoding time   : 0.000
% 29.79/29.98  #    Success case prop solver time     : 0.000
% 29.79/29.98  # Current number of processed clauses  : 1617
% 29.79/29.98  #    Positive orientable unit clauses  : 30
% 29.79/29.98  #    Positive unorientable unit clauses: 0
% 29.79/29.98  #    Negative unit clauses             : 2
% 29.79/29.98  #    Non-unit-clauses                  : 1585
% 29.79/29.98  # Current number of unprocessed clauses: 1520019
% 29.79/29.98  # ...number of literals in the above   : 10195456
% 29.79/29.98  # Current number of archived formulas  : 0
% 29.79/29.98  # Current number of archived clauses   : 1304
% 29.79/29.98  # Clause-clause subsumption calls (NU) : 1303214
% 29.79/29.98  # Rec. Clause-clause subsumption calls : 97744
% 29.79/29.98  # Non-unit clause-clause subsumptions  : 11914
% 29.79/29.98  # Unit Clause-clause subsumption calls : 1792
% 29.79/29.98  # Rewrite failures with RHS unbound    : 0
% 29.79/29.98  # BW rewrite match attempts            : 170
% 29.79/29.98  # BW rewrite match successes           : 13
% 29.79/29.98  # Condensation attempts                : 0
% 29.79/29.98  # Condensation successes               : 0
% 29.79/29.98  # Termbank termtop insertions          : 94007299
% 29.85/30.07  
% 29.85/30.07  # -------------------------------------------------
% 29.85/30.07  # User time                : 28.801 s
% 29.85/30.07  # System time              : 0.910 s
% 29.85/30.07  # Total time               : 29.711 s
% 29.85/30.07  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
