%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:08 EST 2020

% Result     : Timeout 58.92s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   69 (3230 expanded)
%              Number of clauses        :   56 (1432 expanded)
%              Number of leaves         :    6 ( 874 expanded)
%              Depth                    :   25
%              Number of atoms          :  231 (12701 expanded)
%              Number of equality atoms :   67 (5286 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    6 (   1 average)

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X13] :
      ( ( k1_relat_1(X13) != k1_xboole_0
        | X13 = k1_xboole_0
        | ~ v1_relat_1(X13) )
      & ( k2_relat_1(X13) != k1_xboole_0
        | X13 = k1_xboole_0
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_10,plain,(
    ! [X24,X25,X27] :
      ( v1_relat_1(esk5_2(X24,X25))
      & v1_funct_1(esk5_2(X24,X25))
      & k1_relat_1(esk5_2(X24,X25)) = X24
      & ( ~ r2_hidden(X27,X24)
        | k1_funct_1(esk5_2(X24,X25),X27) = X25 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X30] :
      ( ( esk6_0 != k1_xboole_0
        | esk7_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30)
        | esk7_0 != k1_relat_1(X30)
        | ~ r1_tarski(k2_relat_1(X30),esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X18,X19,X20,X22] :
      ( ( r2_hidden(esk2_3(X14,X15,X16),k1_relat_1(X14))
        | ~ r2_hidden(X16,X15)
        | X15 != k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( X16 = k1_funct_1(X14,esk2_3(X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | X15 != k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(X19,k1_relat_1(X14))
        | X18 != k1_funct_1(X14,X19)
        | r2_hidden(X18,X15)
        | X15 != k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(esk3_2(X14,X20),X20)
        | ~ r2_hidden(X22,k1_relat_1(X14))
        | esk3_2(X14,X20) != k1_funct_1(X14,X22)
        | X20 = k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(esk4_2(X14,X20),k1_relat_1(X14))
        | r2_hidden(esk3_2(X14,X20),X20)
        | X20 = k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( esk3_2(X14,X20) = k1_funct_1(X14,esk4_2(X14,X20))
        | r2_hidden(esk3_2(X14,X20),X20)
        | X20 = k2_relat_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v1_relat_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk7_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_funct_1(esk5_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X2,X1),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( esk5_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_19]),c_0_17])])])).

cnf(c_0_24,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( X1 = X2
    | r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X2,X1),X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_13])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_28,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_29,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0),k2_relat_1(esk5_2(esk7_0,X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_xboole_0)
    | ~ r2_hidden(X1,k2_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k2_relat_1(k1_xboole_0),esk6_0),k2_relat_1(k1_xboole_0))
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22]),c_0_22])).

cnf(c_0_34,plain,
    ( k1_funct_1(esk5_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk1_2(k2_relat_1(k1_xboole_0),esk6_0)),k1_xboole_0)
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk1_2(k2_relat_1(k1_xboole_0),esk6_0))) = X1
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_22])).

cnf(c_0_37,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_36])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk4_2(k1_xboole_0,X1),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_38])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_43,plain,
    ( r2_hidden(esk2_3(k1_xboole_0,X1,X2),k1_xboole_0)
    | r2_hidden(esk4_2(k1_xboole_0,X1),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_3(k1_xboole_0,esk6_0,esk1_2(esk6_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,esk6_0,esk1_2(esk6_0,k1_xboole_0))) = X1
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_45]),c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,esk6_0)) = X1
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_49]),c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | ~ r1_tarski(k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_50])).

cnf(c_0_53,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_42])).

cnf(c_0_55,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_16]),c_0_17])])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,esk6_0)) = X1
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_54]),c_0_22])).

cnf(c_0_58,plain,
    ( k1_funct_1(esk5_2(X1,X2),esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3)) = X3
    | ~ r2_hidden(X3,k2_relat_1(esk5_2(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_19]),c_0_17])])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( X1 = X2
    | r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0))) = esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X2),k2_relat_1(esk5_2(esk7_0,X2)),esk1_2(k2_relat_1(esk5_2(esk7_0,X2)),esk6_0))) = X1 ),
    inference(spm,[status(thm)],[c_0_34,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_60])).

cnf(c_0_64,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_65,negated_conjecture,
    ( esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0) = X1 ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_42])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_23])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_66,c_0_67]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 58.92/59.15  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S074A
% 58.92/59.15  # and selection function SelectCQIArEqFirst.
% 58.92/59.15  #
% 58.92/59.15  # Preprocessing time       : 0.028 s
% 58.92/59.15  # Presaturation interreduction done
% 58.92/59.15  
% 58.92/59.15  # Proof found!
% 58.92/59.15  # SZS status Theorem
% 58.92/59.15  # SZS output start CNFRefutation
% 58.92/59.15  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 58.92/59.15  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 58.92/59.15  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 58.92/59.15  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 58.92/59.15  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 58.92/59.15  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 58.92/59.15  fof(c_0_6, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 58.92/59.15  fof(c_0_7, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 58.92/59.15  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 58.92/59.15  fof(c_0_9, plain, ![X13]:((k1_relat_1(X13)!=k1_xboole_0|X13=k1_xboole_0|~v1_relat_1(X13))&(k2_relat_1(X13)!=k1_xboole_0|X13=k1_xboole_0|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 58.92/59.15  fof(c_0_10, plain, ![X24, X25, X27]:(((v1_relat_1(esk5_2(X24,X25))&v1_funct_1(esk5_2(X24,X25)))&k1_relat_1(esk5_2(X24,X25))=X24)&(~r2_hidden(X27,X24)|k1_funct_1(esk5_2(X24,X25),X27)=X25)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 58.92/59.15  fof(c_0_11, negated_conjecture, ![X30]:((esk6_0!=k1_xboole_0|esk7_0=k1_xboole_0)&(~v1_relat_1(X30)|~v1_funct_1(X30)|(esk7_0!=k1_relat_1(X30)|~r1_tarski(k2_relat_1(X30),esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 58.92/59.15  cnf(c_0_12, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 58.92/59.15  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 58.92/59.15  fof(c_0_14, plain, ![X14, X15, X16, X18, X19, X20, X22]:((((r2_hidden(esk2_3(X14,X15,X16),k1_relat_1(X14))|~r2_hidden(X16,X15)|X15!=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(X16=k1_funct_1(X14,esk2_3(X14,X15,X16))|~r2_hidden(X16,X15)|X15!=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(X19,k1_relat_1(X14))|X18!=k1_funct_1(X14,X19)|r2_hidden(X18,X15)|X15!=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&((~r2_hidden(esk3_2(X14,X20),X20)|(~r2_hidden(X22,k1_relat_1(X14))|esk3_2(X14,X20)!=k1_funct_1(X14,X22))|X20=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&((r2_hidden(esk4_2(X14,X20),k1_relat_1(X14))|r2_hidden(esk3_2(X14,X20),X20)|X20=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(esk3_2(X14,X20)=k1_funct_1(X14,esk4_2(X14,X20))|r2_hidden(esk3_2(X14,X20),X20)|X20=k2_relat_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 58.92/59.15  cnf(c_0_15, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 58.92/59.15  cnf(c_0_16, plain, (k1_relat_1(esk5_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 58.92/59.15  cnf(c_0_17, plain, (v1_relat_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 58.92/59.15  cnf(c_0_18, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk7_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 58.92/59.15  cnf(c_0_19, plain, (v1_funct_1(esk5_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 58.92/59.15  cnf(c_0_20, plain, (X1=X2|r2_hidden(esk1_2(X2,X1),X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 58.92/59.15  cnf(c_0_21, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.92/59.15  cnf(c_0_22, plain, (esk5_2(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])])).
% 58.92/59.15  cnf(c_0_23, negated_conjecture, (~r1_tarski(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_16]), c_0_19]), c_0_17])])])).
% 58.92/59.15  cnf(c_0_24, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 58.92/59.15  cnf(c_0_25, plain, (X1=X2|r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X2,X1),X2)), inference(spm,[status(thm)],[c_0_20, c_0_13])).
% 58.92/59.15  cnf(c_0_26, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_21])).
% 58.92/59.15  cnf(c_0_27, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 58.92/59.15  cnf(c_0_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_22])).
% 58.92/59.15  cnf(c_0_29, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_17, c_0_22])).
% 58.92/59.15  cnf(c_0_30, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0),k2_relat_1(esk5_2(esk7_0,X1)))), inference(spm,[status(thm)],[c_0_23, c_0_13])).
% 58.92/59.15  cnf(c_0_31, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25])])).
% 58.92/59.15  cnf(c_0_32, plain, (r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),X1),k1_xboole_0)|~r2_hidden(X1,k2_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 58.92/59.15  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k2_relat_1(k1_xboole_0),esk6_0),k2_relat_1(k1_xboole_0))|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_22]), c_0_22])).
% 58.92/59.15  cnf(c_0_34, plain, (k1_funct_1(esk5_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 58.92/59.15  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk1_2(k2_relat_1(k1_xboole_0),esk6_0)),k1_xboole_0)|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 58.92/59.15  cnf(c_0_36, negated_conjecture, (k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,k2_relat_1(k1_xboole_0),esk1_2(k2_relat_1(k1_xboole_0),esk6_0)))=X1|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_22])).
% 58.92/59.15  cnf(c_0_37, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.92/59.15  cnf(c_0_38, negated_conjecture, (X1=X2|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_36])).
% 58.92/59.15  cnf(c_0_39, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 58.92/59.15  cnf(c_0_40, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk4_2(k1_xboole_0,X1),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_27]), c_0_28]), c_0_29])])).
% 58.92/59.15  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_38])).
% 58.92/59.15  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_39])).
% 58.92/59.15  cnf(c_0_43, plain, (r2_hidden(esk2_3(k1_xboole_0,X1,X2),k1_xboole_0)|r2_hidden(esk4_2(k1_xboole_0,X1),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_32, c_0_40])).
% 58.92/59.15  cnf(c_0_44, negated_conjecture, (r2_hidden(esk1_2(esk6_0,k1_xboole_0),esk6_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 58.92/59.15  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_3(k1_xboole_0,esk6_0,esk1_2(esk6_0,k1_xboole_0)),k1_xboole_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 58.92/59.15  cnf(c_0_46, negated_conjecture, (k1_funct_1(k1_xboole_0,esk2_3(k1_xboole_0,esk6_0,esk1_2(esk6_0,k1_xboole_0)))=X1|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_45]), c_0_22])).
% 58.92/59.15  cnf(c_0_47, negated_conjecture, (X1=X2|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_46])).
% 58.92/59.15  cnf(c_0_48, negated_conjecture, (r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_47])).
% 58.92/59.15  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk4_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_42])).
% 58.92/59.15  cnf(c_0_50, negated_conjecture, (k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,esk6_0))=X1|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_49]), c_0_22])).
% 58.92/59.15  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|~r1_tarski(k1_funct_1(k1_xboole_0,esk4_2(k1_xboole_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_50])).
% 58.92/59.15  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_50])).
% 58.92/59.15  cnf(c_0_53, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 58.92/59.15  cnf(c_0_54, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,esk6_0),k1_xboole_0)|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_42])).
% 58.92/59.15  cnf(c_0_55, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_53])).
% 58.92/59.15  cnf(c_0_56, plain, (r2_hidden(esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3),X1)|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_19]), c_0_16]), c_0_17])])).
% 58.92/59.15  cnf(c_0_57, negated_conjecture, (k1_funct_1(k1_xboole_0,esk1_2(k1_xboole_0,esk6_0))=X1|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_54]), c_0_22])).
% 58.92/59.15  cnf(c_0_58, plain, (k1_funct_1(esk5_2(X1,X2),esk2_3(esk5_2(X1,X2),k2_relat_1(esk5_2(X1,X2)),X3))=X3|~r2_hidden(X3,k2_relat_1(esk5_2(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_19]), c_0_17])])).
% 58.92/59.15  cnf(c_0_59, negated_conjecture, (r2_hidden(esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)),esk7_0)), inference(spm,[status(thm)],[c_0_56, c_0_30])).
% 58.92/59.15  cnf(c_0_60, negated_conjecture, (X1=X2|r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_57])).
% 58.92/59.15  cnf(c_0_61, negated_conjecture, (k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X1),k2_relat_1(esk5_2(esk7_0,X1)),esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)))=esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_30])).
% 58.92/59.15  cnf(c_0_62, negated_conjecture, (k1_funct_1(esk5_2(esk7_0,X1),esk2_3(esk5_2(esk7_0,X2),k2_relat_1(esk5_2(esk7_0,X2)),esk1_2(k2_relat_1(esk5_2(esk7_0,X2)),esk6_0)))=X1), inference(spm,[status(thm)],[c_0_34, c_0_59])).
% 58.92/59.15  cnf(c_0_63, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_60])).
% 58.92/59.15  cnf(c_0_64, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 58.92/59.15  cnf(c_0_65, negated_conjecture, (esk1_2(k2_relat_1(esk5_2(esk7_0,X1)),esk6_0)=X1), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 58.92/59.15  cnf(c_0_66, negated_conjecture, (r2_hidden(esk3_2(k1_xboole_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_63, c_0_42])).
% 58.92/59.15  cnf(c_0_67, negated_conjecture, (~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_23])).
% 58.92/59.15  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_66, c_0_67]), ['proof']).
% 58.92/59.15  # SZS output end CNFRefutation
% 58.92/59.15  # Proof object total steps             : 69
% 58.92/59.15  # Proof object clause steps            : 56
% 58.92/59.15  # Proof object formula steps           : 13
% 58.92/59.15  # Proof object conjectures             : 33
% 58.92/59.15  # Proof object clause conjectures      : 30
% 58.92/59.15  # Proof object formula conjectures     : 3
% 58.92/59.15  # Proof object initial clauses used    : 14
% 58.92/59.15  # Proof object initial formulas used   : 6
% 58.92/59.15  # Proof object generating inferences   : 37
% 58.92/59.15  # Proof object simplifying inferences  : 31
% 58.92/59.15  # Training examples: 0 positive, 0 negative
% 58.92/59.15  # Parsed axioms                        : 6
% 58.92/59.15  # Removed by relevancy pruning/SinE    : 0
% 58.92/59.15  # Initial clauses                      : 20
% 58.92/59.15  # Removed in clause preprocessing      : 0
% 58.92/59.15  # Initial clauses in saturation        : 20
% 58.92/59.15  # Processed clauses                    : 22250
% 58.92/59.15  # ...of these trivial                  : 268
% 58.92/59.15  # ...subsumed                          : 17618
% 58.92/59.15  # ...remaining for further processing  : 4364
% 58.92/59.15  # Other redundant clauses eliminated   : 64103
% 58.92/59.15  # Clauses deleted for lack of memory   : 1814875
% 58.92/59.15  # Backward-subsumed                    : 2165
% 58.92/59.15  # Backward-rewritten                   : 307
% 58.92/59.15  # Generated clauses                    : 4782761
% 58.92/59.15  # ...of the previous two non-trivial   : 4606035
% 58.92/59.15  # Contextual simplify-reflections      : 238
% 58.92/59.15  # Paramodulations                      : 4717855
% 58.92/59.15  # Factorizations                       : 426
% 58.92/59.15  # Equation resolutions                 : 64106
% 58.92/59.15  # Propositional unsat checks           : 0
% 58.92/59.15  #    Propositional check models        : 0
% 58.92/59.15  #    Propositional check unsatisfiable : 0
% 58.92/59.15  #    Propositional clauses             : 0
% 58.92/59.15  #    Propositional clauses after purity: 0
% 58.92/59.15  #    Propositional unsat core size     : 0
% 58.92/59.15  #    Propositional preprocessing time  : 0.000
% 58.92/59.15  #    Propositional encoding time       : 0.000
% 58.92/59.15  #    Propositional solver time         : 0.000
% 58.92/59.15  #    Success case prop preproc time    : 0.000
% 58.92/59.15  #    Success case prop encoding time   : 0.000
% 58.92/59.15  #    Success case prop solver time     : 0.000
% 58.92/59.15  # Current number of processed clauses  : 1493
% 58.92/59.15  #    Positive orientable unit clauses  : 46
% 58.92/59.15  #    Positive unorientable unit clauses: 0
% 58.92/59.15  #    Negative unit clauses             : 2
% 58.92/59.15  #    Non-unit-clauses                  : 1445
% 58.92/59.15  # Current number of unprocessed clauses: 1274539
% 58.92/59.15  # ...number of literals in the above   : 8698228
% 58.92/59.15  # Current number of archived formulas  : 0
% 58.92/59.15  # Current number of archived clauses   : 2866
% 58.92/59.15  # Clause-clause subsumption calls (NU) : 3321930
% 58.92/59.15  # Rec. Clause-clause subsumption calls : 172531
% 58.92/59.15  # Non-unit clause-clause subsumptions  : 19965
% 58.92/59.15  # Unit Clause-clause subsumption calls : 7858
% 58.92/59.15  # Rewrite failures with RHS unbound    : 0
% 58.92/59.15  # BW rewrite match attempts            : 489
% 58.92/59.15  # BW rewrite match successes           : 38
% 58.92/59.15  # Condensation attempts                : 0
% 58.92/59.15  # Condensation successes               : 0
% 58.92/59.15  # Termbank termtop insertions          : 181445295
% 59.05/59.22  
% 59.05/59.22  # -------------------------------------------------
% 59.05/59.22  # User time                : 57.843 s
% 59.05/59.22  # System time              : 1.037 s
% 59.05/59.22  # Total time               : 58.880 s
% 59.05/59.22  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
