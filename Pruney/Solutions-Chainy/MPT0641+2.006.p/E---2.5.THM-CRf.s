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
% DateTime   : Thu Dec  3 10:53:40 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 742 expanded)
%              Number of clauses        :   46 ( 256 expanded)
%              Number of leaves         :    9 ( 177 expanded)
%              Depth                    :   15
%              Number of atoms          :  284 (4595 expanded)
%              Number of equality atoms :   64 ( 689 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & k2_relat_1(X2) = k1_relat_1(X1) )
           => ( v2_funct_1(X2)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t47_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) )
           => v2_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(k5_relat_1(X2,X1))
                & k2_relat_1(X2) = k1_relat_1(X1) )
             => ( v2_funct_1(X2)
                & v2_funct_1(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_funct_1])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ r1_tarski(k2_relat_1(X9),k1_relat_1(X10))
      | k1_relat_1(k5_relat_1(X9,X10)) = k1_relat_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v2_funct_1(k5_relat_1(esk7_0,esk6_0))
    & k2_relat_1(esk7_0) = k1_relat_1(esk6_0)
    & ( ~ v2_funct_1(esk7_0)
      | ~ v2_funct_1(esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_13,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k2_relat_1(esk7_0) = k1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ v2_funct_1(k5_relat_1(X32,X31))
      | ~ r1_tarski(k2_relat_1(X32),k1_relat_1(X31))
      | v2_funct_1(X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v2_funct_1(X21)
        | ~ r2_hidden(X22,k1_relat_1(X21))
        | ~ r2_hidden(X23,k1_relat_1(X21))
        | k1_funct_1(X21,X22) != k1_funct_1(X21,X23)
        | X22 = X23
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk4_1(X21),k1_relat_1(X21))
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk5_1(X21),k1_relat_1(X21))
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( k1_funct_1(X21,esk4_1(X21)) = k1_funct_1(X21,esk5_1(X21))
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( esk4_1(X21) != esk5_1(X21)
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk7_0,X1)) = k1_relat_1(esk7_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X15,X16,X17,X19] :
      ( ( r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X11))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X13 = k1_funct_1(X11,esk1_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | r2_hidden(X15,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk2_2(X11,X17),X17)
        | ~ r2_hidden(X19,k1_relat_1(X11))
        | esk2_2(X11,X17) != k1_funct_1(X11,X19)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk3_2(X11,X17),k1_relat_1(X11))
        | r2_hidden(esk2_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk2_2(X11,X17) = k1_funct_1(X11,esk3_2(X11,X17))
        | r2_hidden(esk2_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_23,plain,
    ( v2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(k5_relat_1(X2,X1))
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( X2 = X3
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk7_0,esk6_0)) = k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_29,plain,(
    ! [X26,X27] :
      ( ( v1_relat_1(k5_relat_1(X26,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( v1_funct_1(k5_relat_1(X26,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk7_0)
    | ~ r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_15]),c_0_21]),c_0_14])])).

cnf(c_0_32,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0))
    | ~ v1_funct_1(k5_relat_1(esk7_0,esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_24])])).

cnf(c_0_33,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_34,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | v1_relat_1(k5_relat_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_funct_1(esk7_0)
    | ~ v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_20])])).

cnf(c_0_38,plain,
    ( X1 = k1_funct_1(X2,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0))
    | ~ v1_relat_1(k5_relat_1(esk7_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26]),c_0_25]),c_0_21]),c_0_15])])).

cnf(c_0_40,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_14]),c_0_25]),c_0_15])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk5_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_funct_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_44,plain,
    ( k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)
    | ~ r2_hidden(X2,k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21]),c_0_15])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)),k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_26]),c_0_21])]),c_0_43])).

cnf(c_0_47,plain,
    ( r2_hidden(esk4_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_48,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ r2_hidden(X28,k1_relat_1(X29))
      | k1_funct_1(k5_relat_1(X29,X30),X28) = k1_funct_1(X30,k1_funct_1(X29,X28)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_14]),c_0_25]),c_0_15])])).

cnf(c_0_50,negated_conjecture,
    ( X1 = esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)),k1_relat_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_47]),c_0_26]),c_0_21])]),c_0_43])).

cnf(c_0_52,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))) = esk5_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_42]),c_0_26]),c_0_21])]),c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)) = esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))) != k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,X1),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))) = k1_funct_1(X1,esk5_1(esk6_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_25]),c_0_15])]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))) = esk4_1(esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_26]),c_0_21])]),c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)) = esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))
    | k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))) != k1_funct_1(esk6_0,esk5_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_26]),c_0_21])])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk7_0,X1),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))) = k1_funct_1(X1,esk4_1(esk6_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_25]),c_0_15])]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)) = esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))
    | k1_funct_1(esk6_0,esk5_1(esk6_0)) != k1_funct_1(esk6_0,esk4_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_26]),c_0_21])])).

cnf(c_0_60,plain,
    ( k1_funct_1(X1,esk4_1(X1)) = k1_funct_1(X1,esk5_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)) = esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_26]),c_0_21])]),c_0_43])).

cnf(c_0_62,plain,
    ( v2_funct_1(X1)
    | esk4_1(X1) != esk5_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( esk5_1(esk6_0) = esk4_1(esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_61]),c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_26]),c_0_21])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.41  # and selection function SelectNewComplexAHPNS.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.027 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t48_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 0.19/0.41  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(t47_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&r1_tarski(k2_relat_1(X2),k1_relat_1(X1)))=>v2_funct_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_funct_1)).
% 0.19/0.41  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 0.19/0.41  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.19/0.41  fof(fc2_funct_1, axiom, ![X1, X2]:((((v1_relat_1(X1)&v1_funct_1(X1))&v1_relat_1(X2))&v1_funct_1(X2))=>(v1_relat_1(k5_relat_1(X1,X2))&v1_funct_1(k5_relat_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 0.19/0.41  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.19/0.41  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 0.19/0.41  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1)))))), inference(assume_negation,[status(cth)],[t48_funct_1])).
% 0.19/0.41  fof(c_0_10, plain, ![X9, X10]:(~v1_relat_1(X9)|(~v1_relat_1(X10)|(~r1_tarski(k2_relat_1(X9),k1_relat_1(X10))|k1_relat_1(k5_relat_1(X9,X10))=k1_relat_1(X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.19/0.41  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((v2_funct_1(k5_relat_1(esk7_0,esk6_0))&k2_relat_1(esk7_0)=k1_relat_1(esk6_0))&(~v2_funct_1(esk7_0)|~v2_funct_1(esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.41  fof(c_0_12, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  cnf(c_0_13, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.41  cnf(c_0_14, negated_conjecture, (k2_relat_1(esk7_0)=k1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_17, plain, ![X31, X32]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~v1_relat_1(X32)|~v1_funct_1(X32)|(~v2_funct_1(k5_relat_1(X32,X31))|~r1_tarski(k2_relat_1(X32),k1_relat_1(X31))|v2_funct_1(X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_funct_1])])])).
% 0.19/0.41  fof(c_0_18, plain, ![X21, X22, X23]:((~v2_funct_1(X21)|(~r2_hidden(X22,k1_relat_1(X21))|~r2_hidden(X23,k1_relat_1(X21))|k1_funct_1(X21,X22)!=k1_funct_1(X21,X23)|X22=X23)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&((((r2_hidden(esk4_1(X21),k1_relat_1(X21))|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(esk5_1(X21),k1_relat_1(X21))|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(k1_funct_1(X21,esk4_1(X21))=k1_funct_1(X21,esk5_1(X21))|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(esk4_1(X21)!=esk5_1(X21)|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.19/0.41  cnf(c_0_19, negated_conjecture, (k1_relat_1(k5_relat_1(esk7_0,X1))=k1_relat_1(esk7_0)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.19/0.41  cnf(c_0_20, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  fof(c_0_22, plain, ![X11, X12, X13, X15, X16, X17, X19]:((((r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X11))|~r2_hidden(X13,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(X13=k1_funct_1(X11,esk1_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(X16,k1_relat_1(X11))|X15!=k1_funct_1(X11,X16)|r2_hidden(X15,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&((~r2_hidden(esk2_2(X11,X17),X17)|(~r2_hidden(X19,k1_relat_1(X11))|esk2_2(X11,X17)!=k1_funct_1(X11,X19))|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&((r2_hidden(esk3_2(X11,X17),k1_relat_1(X11))|r2_hidden(esk2_2(X11,X17),X17)|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(esk2_2(X11,X17)=k1_funct_1(X11,esk3_2(X11,X17))|r2_hidden(esk2_2(X11,X17),X17)|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.19/0.41  cnf(c_0_23, plain, (v2_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(k5_relat_1(X2,X1))|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (v2_funct_1(k5_relat_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_27, plain, (X2=X3|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))|k1_funct_1(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (k1_relat_1(k5_relat_1(esk7_0,esk6_0))=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.19/0.41  fof(c_0_29, plain, ![X26, X27]:((v1_relat_1(k5_relat_1(X26,X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)|~v1_relat_1(X27)|~v1_funct_1(X27)))&(v1_funct_1(k5_relat_1(X26,X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)|~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).
% 0.19/0.41  cnf(c_0_30, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (v2_funct_1(esk7_0)|~r1_tarski(k1_relat_1(esk6_0),k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_15]), c_0_21]), c_0_14])])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)|~r2_hidden(X2,k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))|~v1_funct_1(k5_relat_1(esk7_0,esk6_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_24])])).
% 0.19/0.41  cnf(c_0_33, plain, (v1_funct_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  fof(c_0_34, plain, ![X7, X8]:(~v1_relat_1(X7)|~v1_relat_1(X8)|v1_relat_1(k5_relat_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.19/0.41  cnf(c_0_35, plain, (r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (~v2_funct_1(esk7_0)|~v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (v2_funct_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_20])])).
% 0.19/0.41  cnf(c_0_38, plain, (X1=k1_funct_1(X2,esk1_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)|~r2_hidden(X2,k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))|~v1_relat_1(k5_relat_1(esk7_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26]), c_0_25]), c_0_21]), c_0_15])])).
% 0.19/0.41  cnf(c_0_40, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_14]), c_0_25]), c_0_15])])).
% 0.19/0.41  cnf(c_0_42, plain, (r2_hidden(esk5_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (~v2_funct_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.19/0.41  cnf(c_0_44, plain, (k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2))=X2|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_38])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (X1=X2|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),X2)|~r2_hidden(X2,k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_21]), c_0_15])])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)),k1_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_26]), c_0_21])]), c_0_43])).
% 0.19/0.41  cnf(c_0_47, plain, (r2_hidden(esk4_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_48, plain, ![X28, X29, X30]:(~v1_relat_1(X29)|~v1_funct_1(X29)|(~v1_relat_1(X30)|~v1_funct_1(X30)|(~r2_hidden(X28,k1_relat_1(X29))|k1_funct_1(k5_relat_1(X29,X30),X28)=k1_funct_1(X30,k1_funct_1(X29,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),X1))=X1|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_14]), c_0_25]), c_0_15])])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (X1=esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))|k1_funct_1(k5_relat_1(esk7_0,esk6_0),X1)!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)),k1_relat_1(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_47]), c_0_26]), c_0_21])]), c_0_43])).
% 0.19/0.41  cnf(c_0_52, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))=esk5_1(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_42]), c_0_26]), c_0_21])]), c_0_43])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))=esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))|k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))!=k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.41  cnf(c_0_55, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,X1),esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0)))=k1_funct_1(X1,esk5_1(esk6_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_46]), c_0_25]), c_0_15])]), c_0_53])).
% 0.19/0.41  cnf(c_0_56, negated_conjecture, (k1_funct_1(esk7_0,esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)))=esk4_1(esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_26]), c_0_21])]), c_0_43])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))=esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))|k1_funct_1(k5_relat_1(esk7_0,esk6_0),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)))!=k1_funct_1(esk6_0,esk5_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_26]), c_0_21])])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (k1_funct_1(k5_relat_1(esk7_0,X1),esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0)))=k1_funct_1(X1,esk4_1(esk6_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_51]), c_0_25]), c_0_15])]), c_0_56])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))=esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))|k1_funct_1(esk6_0,esk5_1(esk6_0))!=k1_funct_1(esk6_0,esk4_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_26]), c_0_21])])).
% 0.19/0.41  cnf(c_0_60, plain, (k1_funct_1(X1,esk4_1(X1))=k1_funct_1(X1,esk5_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (esk1_3(esk7_0,k1_relat_1(esk6_0),esk5_1(esk6_0))=esk1_3(esk7_0,k1_relat_1(esk6_0),esk4_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_26]), c_0_21])]), c_0_43])).
% 0.19/0.41  cnf(c_0_62, plain, (v2_funct_1(X1)|esk4_1(X1)!=esk5_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_63, negated_conjecture, (esk5_1(esk6_0)=esk4_1(esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_61]), c_0_56])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_26]), c_0_21])]), c_0_43]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 65
% 0.19/0.41  # Proof object clause steps            : 46
% 0.19/0.41  # Proof object formula steps           : 19
% 0.19/0.41  # Proof object conjectures             : 33
% 0.19/0.41  # Proof object clause conjectures      : 30
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 20
% 0.19/0.41  # Proof object initial formulas used   : 9
% 0.19/0.41  # Proof object generating inferences   : 20
% 0.19/0.41  # Proof object simplifying inferences  : 73
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 9
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 27
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 27
% 0.19/0.41  # Processed clauses                    : 285
% 0.19/0.41  # ...of these trivial                  : 21
% 0.19/0.41  # ...subsumed                          : 28
% 0.19/0.41  # ...remaining for further processing  : 236
% 0.19/0.41  # Other redundant clauses eliminated   : 6
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 45
% 0.19/0.41  # Backward-rewritten                   : 77
% 0.19/0.41  # Generated clauses                    : 783
% 0.19/0.41  # ...of the previous two non-trivial   : 780
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 778
% 0.19/0.41  # Factorizations                       : 0
% 0.19/0.41  # Equation resolutions                 : 6
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 109
% 0.19/0.41  #    Positive orientable unit clauses  : 28
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 1
% 0.19/0.41  #    Non-unit-clauses                  : 80
% 0.19/0.41  # Current number of unprocessed clauses: 489
% 0.19/0.41  # ...number of literals in the above   : 2392
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 122
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 1740
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 623
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 65
% 0.19/0.41  # Unit Clause-clause subsumption calls : 184
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 113
% 0.19/0.41  # BW rewrite match successes           : 16
% 0.19/0.41  # Condensation attempts                : 285
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 36859
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.065 s
% 0.19/0.41  # System time              : 0.003 s
% 0.19/0.41  # Total time               : 0.068 s
% 0.19/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
