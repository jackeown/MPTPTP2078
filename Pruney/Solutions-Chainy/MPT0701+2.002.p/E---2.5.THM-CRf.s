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
% DateTime   : Thu Dec  3 10:55:06 EST 2020

% Result     : Theorem 6.46s
% Output     : CNFRefutation 6.46s
% Verified   : 
% Statistics : Number of formulae       :  127 (82605 expanded)
%              Number of clauses        :  112 (31235 expanded)
%              Number of leaves         :    7 (19564 expanded)
%              Depth                    :   49
%              Number of atoms          :  396 (579465 expanded)
%              Number of equality atoms :  145 (210838 expanded)
%              Maximal formula depth    :   18 (   3 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t156_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( v1_relat_1(X4)
                & v1_funct_1(X4) )
             => ( ( X1 = k2_relat_1(X2)
                  & k1_relat_1(X3) = X1
                  & k1_relat_1(X4) = X1
                  & k5_relat_1(X2,X3) = k5_relat_1(X2,X4) )
               => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_1)).

fof(d3_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_tarski(X1,X2)
        <=> ! [X3,X4] :
              ( r2_hidden(k4_tarski(X3,X4),X1)
             => r2_hidden(k4_tarski(X3,X4),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

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

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( v1_relat_1(X4)
                  & v1_funct_1(X4) )
               => ( ( X1 = k2_relat_1(X2)
                    & k1_relat_1(X3) = X1
                    & k1_relat_1(X4) = X1
                    & k5_relat_1(X2,X3) = k5_relat_1(X2,X4) )
                 => X3 = X4 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t156_funct_1])).

fof(c_0_8,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(k4_tarski(X9,X10),X7)
        | r2_hidden(k4_tarski(X9,X10),X8)
        | ~ v1_relat_1(X7) )
      & ( r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X7)
        | r1_tarski(X7,X11)
        | ~ v1_relat_1(X7) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X11)
        | r1_tarski(X7,X11)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & v1_relat_1(esk9_0)
    & v1_funct_1(esk9_0)
    & esk6_0 = k2_relat_1(esk7_0)
    & k1_relat_1(esk8_0) = esk6_0
    & k1_relat_1(esk9_0) = esk6_0
    & k5_relat_1(esk7_0,esk8_0) = k5_relat_1(esk7_0,esk9_0)
    & esk8_0 != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)),esk9_0)
    | r1_tarski(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X30,X31,X32] :
      ( ( r2_hidden(X30,k1_relat_1(X32))
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( X31 = k1_funct_1(X32,X30)
        | ~ r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( ~ r2_hidden(X30,k1_relat_1(X32))
        | X31 != k1_funct_1(X32,X30)
        | r2_hidden(k4_tarski(X30,X31),X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_17,plain,(
    ! [X14,X15,X16] :
      ( ( r2_hidden(X14,k1_relat_1(X16))
        | ~ r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(X15,k2_relat_1(X16))
        | ~ r2_hidden(k4_tarski(X14,X15),X16)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_18,negated_conjecture,
    ( X1 = esk9_0
    | r2_hidden(k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)),esk9_0)
    | ~ r1_tarski(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)
    | r1_tarski(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)
    | r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_12])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk8_0,X1)),esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_15])])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_27]),c_0_15])])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X3,X4),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X4),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_29]),c_0_26]),c_0_15])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),esk8_0)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(X1,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)
    | ~ r1_tarski(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_15])])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_38]),c_0_12])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_12])])).

fof(c_0_43,plain,(
    ! [X17,X18,X19,X21,X22,X23,X25] :
      ( ( r2_hidden(esk3_3(X17,X18,X19),k1_relat_1(X17))
        | ~ r2_hidden(X19,X18)
        | X18 != k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( X19 = k1_funct_1(X17,esk3_3(X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | X18 != k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X22,k1_relat_1(X17))
        | X21 != k1_funct_1(X17,X22)
        | r2_hidden(X21,X18)
        | X18 != k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(esk4_2(X17,X23),X23)
        | ~ r2_hidden(X25,k1_relat_1(X17))
        | esk4_2(X17,X23) != k1_funct_1(X17,X25)
        | X23 = k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk5_2(X17,X23),k1_relat_1(X17))
        | r2_hidden(esk4_2(X17,X23),X23)
        | X23 = k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk4_2(X17,X23) = k1_funct_1(X17,esk5_2(X17,X23))
        | r2_hidden(esk4_2(X17,X23),X23)
        | X23 = k2_relat_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_41]),c_0_27]),c_0_15])])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_42]),c_0_27]),c_0_15])])).

cnf(c_0_47,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)
    | r2_hidden(esk1_2(esk8_0,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_44]),c_0_26]),c_0_15])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(esk9_0,X1)),esk9_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_38]),c_0_12])])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_41]),c_0_26]),c_0_15])])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( esk6_0 = k2_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(X1,esk1_2(esk9_0,esk8_0))
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)
    | r2_hidden(esk1_2(esk8_0,X1),esk6_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_51])).

fof(c_0_60,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ r2_hidden(X27,k1_relat_1(X28))
      | k1_funct_1(k5_relat_1(X28,X29),X27) = k1_funct_1(X29,k1_funct_1(X28,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,esk6_0,X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_38]),c_0_12])])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),X1)
    | ~ r1_tarski(esk9_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_57]),c_0_12])])).

cnf(c_0_64,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)
    | ~ r1_tarski(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_19])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r1_tarski(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_12])])).

cnf(c_0_66,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | r2_hidden(esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( X1 = k1_funct_1(X2,esk3_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),X1)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_20])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,X1),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))) = k1_funct_1(X1,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_54]),c_0_55])])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(esk7_0,esk8_0) = k5_relat_1(esk7_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_73,plain,
    ( k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0)) = k1_funct_1(X1,esk1_2(esk8_0,esk9_0))
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)),esk9_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_70]),c_0_27]),c_0_15])])).

cnf(c_0_76,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))) = k1_funct_1(esk9_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_38]),c_0_72]),c_0_12])])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))) = k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_27]),c_0_15])])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,X1)) = X1
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_79,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_27]),c_0_15])]),c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)))) = k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))) = esk1_2(esk8_0,esk9_0)
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_62])).

cnf(c_0_82,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0)
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_79]),c_0_38]),c_0_12])])).

cnf(c_0_83,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_62])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_87,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r1_tarski(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_86]),c_0_15])])).

cnf(c_0_88,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_87]),c_0_20])).

cnf(c_0_90,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r1_tarski(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_88]),c_0_15])])).

cnf(c_0_91,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_89]),c_0_24]),c_0_12])])).

cnf(c_0_92,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_90]),c_0_20])).

cnf(c_0_93,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_92]),c_0_38]),c_0_12])])).

cnf(c_0_95,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = esk1_2(esk9_0,esk8_0)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_35])).

cnf(c_0_97,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_95]),c_0_24]),c_0_12])])).

cnf(c_0_98,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = esk1_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_96])).

cnf(c_0_99,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_97])).

cnf(c_0_100,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = esk1_2(esk9_0,esk8_0)
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_85])).

cnf(c_0_101,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,X1),esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = k1_funct_1(X1,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_99]),c_0_54]),c_0_55])])).

cnf(c_0_102,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = esk1_2(esk9_0,esk8_0)
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r1_tarski(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_100]),c_0_15])])).

cnf(c_0_103,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = k1_funct_1(esk9_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_38]),c_0_72]),c_0_12])])).

cnf(c_0_104,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_27]),c_0_15])])).

cnf(c_0_105,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = esk1_2(esk9_0,esk8_0)
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0)
    | r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_102]),c_0_20])).

cnf(c_0_106,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))) = k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))) = esk1_2(esk9_0,esk8_0)
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_105]),c_0_24]),c_0_12])]),c_0_78])).

cnf(c_0_108,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0)) = k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))
    | k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_109,negated_conjecture,
    ( k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0)) = esk2_2(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_108])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk8_0)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_109])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)
    | r1_tarski(esk9_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_110]),c_0_12])])).

cnf(c_0_112,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)
    | r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_111]),c_0_20])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_112]),c_0_26]),c_0_15])])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)),k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_113])).

cnf(c_0_115,negated_conjecture,
    ( k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))) = esk1_2(esk8_0,esk9_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,X1),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))) = k1_funct_1(X1,esk1_2(esk8_0,esk9_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_114]),c_0_54]),c_0_55])]),c_0_115])).

cnf(c_0_117,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))) = esk2_2(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_27]),c_0_75]),c_0_15])])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),esk9_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0)) = esk2_2(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_38]),c_0_72]),c_0_12])]),c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk9_0) ),
    inference(rw,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_121,negated_conjecture,
    ( r1_tarski(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_120]),c_0_15])])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_121]),c_0_20])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_122]),c_0_24]),c_0_12])])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_123]),c_0_109])).

cnf(c_0_125,negated_conjecture,
    ( ~ r1_tarski(esk9_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_121]),c_0_20])).

cnf(c_0_126,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_124]),c_0_12])]),c_0_125]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 6.46/6.67  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 6.46/6.67  # and selection function SelectComplexG.
% 6.46/6.67  #
% 6.46/6.67  # Preprocessing time       : 0.027 s
% 6.46/6.67  # Presaturation interreduction done
% 6.46/6.67  
% 6.46/6.67  # Proof found!
% 6.46/6.67  # SZS status Theorem
% 6.46/6.67  # SZS output start CNFRefutation
% 6.46/6.67  fof(t156_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>![X4]:((v1_relat_1(X4)&v1_funct_1(X4))=>((((X1=k2_relat_1(X2)&k1_relat_1(X3)=X1)&k1_relat_1(X4)=X1)&k5_relat_1(X2,X3)=k5_relat_1(X2,X4))=>X3=X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_1)).
% 6.46/6.67  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relat_1)).
% 6.46/6.67  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.46/6.67  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 6.46/6.67  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 6.46/6.67  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 6.46/6.67  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 6.46/6.67  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>![X4]:((v1_relat_1(X4)&v1_funct_1(X4))=>((((X1=k2_relat_1(X2)&k1_relat_1(X3)=X1)&k1_relat_1(X4)=X1)&k5_relat_1(X2,X3)=k5_relat_1(X2,X4))=>X3=X4))))), inference(assume_negation,[status(cth)],[t156_funct_1])).
% 6.46/6.67  fof(c_0_8, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(k4_tarski(X9,X10),X7)|r2_hidden(k4_tarski(X9,X10),X8))|~v1_relat_1(X7))&((r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X7)|r1_tarski(X7,X11)|~v1_relat_1(X7))&(~r2_hidden(k4_tarski(esk1_2(X7,X11),esk2_2(X7,X11)),X11)|r1_tarski(X7,X11)|~v1_relat_1(X7)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 6.46/6.67  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&((v1_relat_1(esk9_0)&v1_funct_1(esk9_0))&((((esk6_0=k2_relat_1(esk7_0)&k1_relat_1(esk8_0)=esk6_0)&k1_relat_1(esk9_0)=esk6_0)&k5_relat_1(esk7_0,esk8_0)=k5_relat_1(esk7_0,esk9_0))&esk8_0!=esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 6.46/6.67  fof(c_0_10, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 6.46/6.67  cnf(c_0_11, plain, (r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 6.46/6.67  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_13, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 6.46/6.67  cnf(c_0_14, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)),esk9_0)|r1_tarski(esk9_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 6.46/6.67  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  fof(c_0_16, plain, ![X30, X31, X32]:(((r2_hidden(X30,k1_relat_1(X32))|~r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(X31=k1_funct_1(X32,X30)|~r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(~r2_hidden(X30,k1_relat_1(X32))|X31!=k1_funct_1(X32,X30)|r2_hidden(k4_tarski(X30,X31),X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 6.46/6.67  fof(c_0_17, plain, ![X14, X15, X16]:((r2_hidden(X14,k1_relat_1(X16))|~r2_hidden(k4_tarski(X14,X15),X16)|~v1_relat_1(X16))&(r2_hidden(X15,k2_relat_1(X16))|~r2_hidden(k4_tarski(X14,X15),X16)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 6.46/6.67  cnf(c_0_18, negated_conjecture, (X1=esk9_0|r2_hidden(k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)),esk9_0)|~r1_tarski(X1,esk9_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 6.46/6.67  cnf(c_0_19, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)|r1_tarski(esk8_0,X1)), inference(spm,[status(thm)],[c_0_11, c_0_15])).
% 6.46/6.67  cnf(c_0_20, negated_conjecture, (esk8_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.46/6.67  cnf(c_0_22, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 6.46/6.67  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 6.46/6.67  cnf(c_0_24, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_21])).
% 6.46/6.67  cnf(c_0_26, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_27, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_28, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 6.46/6.67  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)|r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_12])])).
% 6.46/6.67  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk8_0,X1)),esk8_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_15])])).
% 6.46/6.67  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_27]), c_0_15])])).
% 6.46/6.67  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X3,X4),X2)|~r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X3,X4),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 6.46/6.67  cnf(c_0_33, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 6.46/6.67  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)|~r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_15])])).
% 6.46/6.67  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_29]), c_0_26]), c_0_15])])).
% 6.46/6.67  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)|r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)), inference(spm,[status(thm)],[c_0_34, c_0_19])).
% 6.46/6.67  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),esk8_0)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_35])).
% 6.46/6.67  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(X1,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_36])).
% 6.46/6.67  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)|~r1_tarski(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_15])])).
% 6.46/6.67  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_38]), c_0_12])])).
% 6.46/6.67  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_12])])).
% 6.46/6.67  fof(c_0_43, plain, ![X17, X18, X19, X21, X22, X23, X25]:((((r2_hidden(esk3_3(X17,X18,X19),k1_relat_1(X17))|~r2_hidden(X19,X18)|X18!=k2_relat_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(X19=k1_funct_1(X17,esk3_3(X17,X18,X19))|~r2_hidden(X19,X18)|X18!=k2_relat_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(X22,k1_relat_1(X17))|X21!=k1_funct_1(X17,X22)|r2_hidden(X21,X18)|X18!=k2_relat_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&((~r2_hidden(esk4_2(X17,X23),X23)|(~r2_hidden(X25,k1_relat_1(X17))|esk4_2(X17,X23)!=k1_funct_1(X17,X25))|X23=k2_relat_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&((r2_hidden(esk5_2(X17,X23),k1_relat_1(X17))|r2_hidden(esk4_2(X17,X23),X23)|X23=k2_relat_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(esk4_2(X17,X23)=k1_funct_1(X17,esk5_2(X17,X23))|r2_hidden(esk4_2(X17,X23),X23)|X23=k2_relat_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 6.46/6.67  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)|r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_19])).
% 6.46/6.67  cnf(c_0_45, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_41]), c_0_27]), c_0_15])])).
% 6.46/6.67  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_42]), c_0_27]), c_0_15])])).
% 6.46/6.67  cnf(c_0_47, plain, (r2_hidden(esk3_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 6.46/6.67  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))),X1)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)|r2_hidden(esk1_2(esk8_0,X1),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_44]), c_0_26]), c_0_15])])).
% 6.46/6.67  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(X1,k1_funct_1(esk9_0,X1)),esk9_0)|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_24]), c_0_38]), c_0_12])])).
% 6.46/6.67  cnf(c_0_50, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_41]), c_0_26]), c_0_15])])).
% 6.46/6.67  cnf(c_0_51, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 6.46/6.67  cnf(c_0_52, plain, (r2_hidden(esk3_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_47])).
% 6.46/6.67  cnf(c_0_53, negated_conjecture, (esk6_0=k2_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_56, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(X1,esk1_2(esk9_0,esk8_0))|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)|r2_hidden(esk1_2(esk8_0,X1),esk6_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 6.46/6.67  cnf(c_0_57, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),esk9_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 6.46/6.67  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 6.46/6.67  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_51])).
% 6.46/6.67  fof(c_0_60, plain, ![X27, X28, X29]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)|(~r2_hidden(X27,k1_relat_1(X28))|k1_funct_1(k5_relat_1(X28,X29),X27)=k1_funct_1(X29,k1_funct_1(X28,X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 6.46/6.67  cnf(c_0_61, negated_conjecture, (r2_hidden(esk3_3(esk7_0,esk6_0,X1),k1_relat_1(esk7_0))|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55])])).
% 6.46/6.67  cnf(c_0_62, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_38]), c_0_12])])).
% 6.46/6.67  cnf(c_0_63, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),X1)|~r1_tarski(esk9_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_57]), c_0_12])])).
% 6.46/6.67  cnf(c_0_64, negated_conjecture, (X1=esk8_0|r2_hidden(k4_tarski(esk1_2(esk8_0,X1),esk2_2(esk8_0,X1)),esk8_0)|~r1_tarski(X1,esk8_0)), inference(spm,[status(thm)],[c_0_13, c_0_19])).
% 6.46/6.67  cnf(c_0_65, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r1_tarski(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_12])])).
% 6.46/6.67  cnf(c_0_66, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 6.46/6.67  cnf(c_0_67, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|r2_hidden(esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 6.46/6.67  cnf(c_0_68, plain, (X1=k1_funct_1(X2,esk3_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 6.46/6.67  cnf(c_0_69, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),X1)|r2_hidden(k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)),esk9_0)), inference(spm,[status(thm)],[c_0_63, c_0_14])).
% 6.46/6.67  cnf(c_0_70, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_20])).
% 6.46/6.67  cnf(c_0_71, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,X1),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)))=k1_funct_1(X1,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_54]), c_0_55])])).
% 6.46/6.67  cnf(c_0_72, negated_conjecture, (k5_relat_1(esk7_0,esk8_0)=k5_relat_1(esk7_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 6.46/6.67  cnf(c_0_73, plain, (k1_funct_1(X1,esk3_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_68])).
% 6.46/6.67  cnf(c_0_74, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))=k1_funct_1(X1,esk1_2(esk8_0,esk9_0))|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,X1),esk2_2(esk9_0,X1)),esk9_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_69])).
% 6.46/6.67  cnf(c_0_75, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_70]), c_0_27]), c_0_15])])).
% 6.46/6.67  cnf(c_0_76, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)))=k1_funct_1(esk9_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_38]), c_0_72]), c_0_12])])).
% 6.46/6.67  cnf(c_0_77, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)))=k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_27]), c_0_15])])).
% 6.46/6.67  cnf(c_0_78, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,X1))=X1|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_53]), c_0_54]), c_0_55])])).
% 6.46/6.67  cnf(c_0_79, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_27]), c_0_15])]), c_0_75])).
% 6.46/6.67  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk9_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))=k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0))))|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 6.46/6.67  cnf(c_0_81, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)))=esk1_2(esk8_0,esk9_0)|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_78, c_0_62])).
% 6.46/6.67  cnf(c_0_82, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_79]), c_0_38]), c_0_12])])).
% 6.46/6.67  cnf(c_0_83, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_75])).
% 6.46/6.67  cnf(c_0_84, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),esk9_0)), inference(spm,[status(thm)],[c_0_49, c_0_62])).
% 6.46/6.67  cnf(c_0_85, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 6.46/6.67  cnf(c_0_86, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk9_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 6.46/6.67  cnf(c_0_87, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r1_tarski(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_86]), c_0_15])])).
% 6.46/6.67  cnf(c_0_88, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk9_0)), inference(spm,[status(thm)],[c_0_57, c_0_85])).
% 6.46/6.67  cnf(c_0_89, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_87]), c_0_20])).
% 6.46/6.67  cnf(c_0_90, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r1_tarski(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_88]), c_0_15])])).
% 6.46/6.67  cnf(c_0_91, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_89]), c_0_24]), c_0_12])])).
% 6.46/6.67  cnf(c_0_92, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_90]), c_0_20])).
% 6.46/6.67  cnf(c_0_93, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))),esk9_0)), inference(spm,[status(thm)],[c_0_49, c_0_91])).
% 6.46/6.67  cnf(c_0_94, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_92]), c_0_38]), c_0_12])])).
% 6.46/6.67  cnf(c_0_95, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 6.46/6.67  cnf(c_0_96, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=esk1_2(esk9_0,esk8_0)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(spm,[status(thm)],[c_0_78, c_0_35])).
% 6.46/6.67  cnf(c_0_97, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_95]), c_0_24]), c_0_12])])).
% 6.46/6.67  cnf(c_0_98, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=esk1_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),esk9_0)), inference(spm,[status(thm)],[c_0_49, c_0_96])).
% 6.46/6.67  cnf(c_0_99, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_61, c_0_97])).
% 6.46/6.67  cnf(c_0_100, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=esk1_2(esk9_0,esk8_0)|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk9_0)), inference(spm,[status(thm)],[c_0_98, c_0_85])).
% 6.46/6.67  cnf(c_0_101, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,X1),esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=k1_funct_1(X1,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_99]), c_0_54]), c_0_55])])).
% 6.46/6.67  cnf(c_0_102, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=esk1_2(esk9_0,esk8_0)|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r1_tarski(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_100]), c_0_15])])).
% 6.46/6.67  cnf(c_0_103, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=k1_funct_1(esk9_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_38]), c_0_72]), c_0_12])])).
% 6.46/6.67  cnf(c_0_104, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_27]), c_0_15])])).
% 6.46/6.67  cnf(c_0_105, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=esk1_2(esk9_0,esk8_0)|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)|r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_102]), c_0_20])).
% 6.46/6.67  cnf(c_0_106, negated_conjecture, (k1_funct_1(esk9_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))=k1_funct_1(esk8_0,k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0))))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 6.46/6.67  cnf(c_0_107, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk9_0,esk8_0)))=esk1_2(esk9_0,esk8_0)|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_105]), c_0_24]), c_0_12])]), c_0_78])).
% 6.46/6.67  cnf(c_0_108, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk9_0,esk8_0))=k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))|k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_106, c_0_107])).
% 6.46/6.67  cnf(c_0_109, negated_conjecture, (k1_funct_1(esk8_0,esk1_2(esk9_0,esk8_0))=esk2_2(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_94, c_0_108])).
% 6.46/6.67  cnf(c_0_110, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk8_0)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(rw,[status(thm)],[c_0_37, c_0_109])).
% 6.46/6.67  cnf(c_0_111, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)|r1_tarski(esk9_0,esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_110]), c_0_12])])).
% 6.46/6.67  cnf(c_0_112, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk8_0)|r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_111]), c_0_20])).
% 6.46/6.67  cnf(c_0_113, negated_conjecture, (r2_hidden(esk1_2(esk8_0,esk9_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_112]), c_0_26]), c_0_15])])).
% 6.46/6.67  cnf(c_0_114, negated_conjecture, (r2_hidden(esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)),k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_61, c_0_113])).
% 6.46/6.67  cnf(c_0_115, negated_conjecture, (k1_funct_1(esk7_0,esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)))=esk1_2(esk8_0,esk9_0)), inference(spm,[status(thm)],[c_0_78, c_0_113])).
% 6.46/6.67  cnf(c_0_116, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,X1),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)))=k1_funct_1(X1,esk1_2(esk8_0,esk9_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_114]), c_0_54]), c_0_55])]), c_0_115])).
% 6.46/6.67  cnf(c_0_117, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,esk8_0),esk3_3(esk7_0,esk6_0,esk1_2(esk8_0,esk9_0)))=esk2_2(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_27]), c_0_75]), c_0_15])])).
% 6.46/6.67  cnf(c_0_118, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))),esk9_0)), inference(spm,[status(thm)],[c_0_49, c_0_113])).
% 6.46/6.67  cnf(c_0_119, negated_conjecture, (k1_funct_1(esk9_0,esk1_2(esk8_0,esk9_0))=esk2_2(esk8_0,esk9_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_38]), c_0_72]), c_0_12])]), c_0_117])).
% 6.46/6.67  cnf(c_0_120, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk8_0,esk9_0),esk2_2(esk8_0,esk9_0)),esk9_0)), inference(rw,[status(thm)],[c_0_118, c_0_119])).
% 6.46/6.67  cnf(c_0_121, negated_conjecture, (r1_tarski(esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_120]), c_0_15])])).
% 6.46/6.67  cnf(c_0_122, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_121]), c_0_20])).
% 6.46/6.67  cnf(c_0_123, negated_conjecture, (r2_hidden(esk1_2(esk9_0,esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_122]), c_0_24]), c_0_12])])).
% 6.46/6.67  cnf(c_0_124, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk9_0,esk8_0),esk2_2(esk9_0,esk8_0)),esk8_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_123]), c_0_109])).
% 6.46/6.67  cnf(c_0_125, negated_conjecture, (~r1_tarski(esk9_0,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_121]), c_0_20])).
% 6.46/6.67  cnf(c_0_126, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_124]), c_0_12])]), c_0_125]), ['proof']).
% 6.46/6.67  # SZS output end CNFRefutation
% 6.46/6.67  # Proof object total steps             : 127
% 6.46/6.67  # Proof object clause steps            : 112
% 6.46/6.67  # Proof object formula steps           : 15
% 6.46/6.67  # Proof object conjectures             : 102
% 6.46/6.67  # Proof object clause conjectures      : 99
% 6.46/6.67  # Proof object formula conjectures     : 3
% 6.46/6.67  # Proof object initial clauses used    : 21
% 6.46/6.67  # Proof object initial formulas used   : 7
% 6.46/6.67  # Proof object generating inferences   : 86
% 6.46/6.67  # Proof object simplifying inferences  : 131
% 6.46/6.67  # Training examples: 0 positive, 0 negative
% 6.46/6.67  # Parsed axioms                        : 7
% 6.46/6.67  # Removed by relevancy pruning/SinE    : 0
% 6.46/6.67  # Initial clauses                      : 29
% 6.46/6.67  # Removed in clause preprocessing      : 0
% 6.46/6.67  # Initial clauses in saturation        : 29
% 6.46/6.67  # Processed clauses                    : 24416
% 6.46/6.67  # ...of these trivial                  : 16
% 6.46/6.67  # ...subsumed                          : 8021
% 6.46/6.67  # ...remaining for further processing  : 16379
% 6.46/6.67  # Other redundant clauses eliminated   : 7
% 6.46/6.67  # Clauses deleted for lack of memory   : 0
% 6.46/6.67  # Backward-subsumed                    : 1677
% 6.46/6.67  # Backward-rewritten                   : 8033
% 6.46/6.67  # Generated clauses                    : 216155
% 6.46/6.67  # ...of the previous two non-trivial   : 219218
% 6.46/6.67  # Contextual simplify-reflections      : 14
% 6.46/6.67  # Paramodulations                      : 216145
% 6.46/6.67  # Factorizations                       : 4
% 6.46/6.67  # Equation resolutions                 : 7
% 6.46/6.67  # Propositional unsat checks           : 0
% 6.46/6.67  #    Propositional check models        : 0
% 6.46/6.67  #    Propositional check unsatisfiable : 0
% 6.46/6.67  #    Propositional clauses             : 0
% 6.46/6.67  #    Propositional clauses after purity: 0
% 6.46/6.67  #    Propositional unsat core size     : 0
% 6.46/6.67  #    Propositional preprocessing time  : 0.000
% 6.46/6.67  #    Propositional encoding time       : 0.000
% 6.46/6.67  #    Propositional solver time         : 0.000
% 6.46/6.67  #    Success case prop preproc time    : 0.000
% 6.46/6.67  #    Success case prop encoding time   : 0.000
% 6.46/6.67  #    Success case prop solver time     : 0.000
% 6.46/6.67  # Current number of processed clauses  : 6636
% 6.46/6.67  #    Positive orientable unit clauses  : 48
% 6.46/6.67  #    Positive unorientable unit clauses: 0
% 6.46/6.67  #    Negative unit clauses             : 2
% 6.46/6.67  #    Non-unit-clauses                  : 6586
% 6.46/6.67  # Current number of unprocessed clauses: 193269
% 6.46/6.67  # ...number of literals in the above   : 938229
% 6.46/6.67  # Current number of archived formulas  : 0
% 6.46/6.67  # Current number of archived clauses   : 9737
% 6.46/6.67  # Clause-clause subsumption calls (NU) : 7281529
% 6.46/6.67  # Rec. Clause-clause subsumption calls : 559531
% 6.46/6.67  # Non-unit clause-clause subsumptions  : 8619
% 6.46/6.67  # Unit Clause-clause subsumption calls : 172606
% 6.46/6.67  # Rewrite failures with RHS unbound    : 0
% 6.46/6.67  # BW rewrite match attempts            : 997
% 6.46/6.67  # BW rewrite match successes           : 33
% 6.46/6.67  # Condensation attempts                : 0
% 6.46/6.67  # Condensation successes               : 0
% 6.46/6.67  # Termbank termtop insertions          : 5781109
% 6.46/6.68  
% 6.46/6.68  # -------------------------------------------------
% 6.46/6.68  # User time                : 6.238 s
% 6.46/6.68  # System time              : 0.102 s
% 6.46/6.68  # Total time               : 6.340 s
% 6.46/6.68  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
