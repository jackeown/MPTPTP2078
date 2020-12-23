%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:07 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 508 expanded)
%              Number of clauses        :   32 ( 164 expanded)
%              Number of leaves         :    5 ( 121 expanded)
%              Depth                    :   11
%              Number of atoms          :  214 (4199 expanded)
%              Number of equality atoms :   62 (1781 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X5,X6,X7,X9,X10,X11,X13] :
      ( ( r2_hidden(esk1_3(X5,X6,X7),k1_relat_1(X5))
        | ~ r2_hidden(X7,X6)
        | X6 != k2_relat_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( X7 = k1_funct_1(X5,esk1_3(X5,X6,X7))
        | ~ r2_hidden(X7,X6)
        | X6 != k2_relat_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( ~ r2_hidden(X10,k1_relat_1(X5))
        | X9 != k1_funct_1(X5,X10)
        | r2_hidden(X9,X6)
        | X6 != k2_relat_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( ~ r2_hidden(esk2_2(X5,X11),X11)
        | ~ r2_hidden(X13,k1_relat_1(X5))
        | esk2_2(X5,X11) != k1_funct_1(X5,X13)
        | X11 = k2_relat_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(esk3_2(X5,X11),k1_relat_1(X5))
        | r2_hidden(esk2_2(X5,X11),X11)
        | X11 = k2_relat_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( esk2_2(X5,X11) = k1_funct_1(X5,esk3_2(X5,X11))
        | r2_hidden(esk2_2(X5,X11),X11)
        | X11 = k2_relat_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_7,plain,(
    ! [X21,X22] :
      ( ( r2_hidden(esk4_2(X21,X22),k1_relat_1(X21))
        | k1_relat_1(X21) != k1_relat_1(X22)
        | X21 = X22
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( k1_funct_1(X21,esk4_2(X21,X22)) != k1_funct_1(X22,esk4_2(X21,X22))
        | k1_relat_1(X21) != k1_relat_1(X22)
        | X21 = X22
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & esk5_0 = k2_relat_1(esk6_0)
    & k1_relat_1(esk7_0) = esk5_0
    & k1_relat_1(esk8_0) = esk5_0
    & k5_relat_1(esk6_0,esk7_0) = k5_relat_1(esk6_0,esk8_0)
    & esk7_0 != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

cnf(c_0_9,plain,
    ( X1 = k1_funct_1(X2,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,plain,
    ( k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( esk5_0 = k2_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( X1 = esk8_0
    | r2_hidden(esk4_2(X1,esk8_0),k1_relat_1(X1))
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( esk7_0 != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X15,X16,X17] :
      ( ( r2_hidden(X15,k1_relat_1(X17))
        | ~ r2_hidden(X15,k1_relat_1(k5_relat_1(X17,X16)))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(k1_funct_1(X17,X15),k1_relat_1(X16))
        | ~ r2_hidden(X15,k1_relat_1(k5_relat_1(X17,X16)))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X15,k1_relat_1(X17))
        | ~ r2_hidden(k1_funct_1(X17,X15),k1_relat_1(X16))
        | r2_hidden(X15,k1_relat_1(k5_relat_1(X17,X16)))
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_3(esk6_0,esk5_0,X1)) = X1
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,esk5_0,X1),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0))) = esk4_2(esk7_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_27])).

fof(c_0_32,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ r2_hidden(X18,k1_relat_1(k5_relat_1(X20,X19)))
      | k1_funct_1(k5_relat_1(X20,X19),X18) = k1_funct_1(X19,k1_funct_1(X20,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0)),k1_relat_1(k5_relat_1(esk6_0,X1)))
    | ~ r2_hidden(esk4_2(esk7_0,esk8_0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_17]),c_0_18])])).

cnf(c_0_34,negated_conjecture,
    ( k5_relat_1(esk6_0,esk7_0) = k5_relat_1(esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0)),k1_relat_1(k5_relat_1(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_12]),c_0_34]),c_0_27]),c_0_11]),c_0_13])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk4_2(X1,X2)) != k1_funct_1(X2,esk4_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,esk7_0),X1) = k1_funct_1(esk8_0,k1_funct_1(esk6_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(esk6_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_34]),c_0_17]),c_0_11]),c_0_18]),c_0_13])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0))) = k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30]),c_0_17]),c_0_21]),c_0_18]),c_0_22])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = esk8_0
    | k1_funct_1(X1,esk4_2(X1,esk8_0)) != k1_funct_1(esk8_0,esk4_2(X1,esk8_0))
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_11]),c_0_12]),c_0_13])])).

cnf(c_0_41,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_2(esk7_0,esk8_0)) = k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_30]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:23:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S064I
% 0.12/0.37  # and selection function SelectComplexG.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t156_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>![X4]:((v1_relat_1(X4)&v1_funct_1(X4))=>((((X1=k2_relat_1(X2)&k1_relat_1(X3)=X1)&k1_relat_1(X4)=X1)&k5_relat_1(X2,X3)=k5_relat_1(X2,X4))=>X3=X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_1)).
% 0.12/0.37  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.12/0.37  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.12/0.37  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 0.12/0.37  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.12/0.37  fof(c_0_5, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>![X4]:((v1_relat_1(X4)&v1_funct_1(X4))=>((((X1=k2_relat_1(X2)&k1_relat_1(X3)=X1)&k1_relat_1(X4)=X1)&k5_relat_1(X2,X3)=k5_relat_1(X2,X4))=>X3=X4))))), inference(assume_negation,[status(cth)],[t156_funct_1])).
% 0.12/0.37  fof(c_0_6, plain, ![X5, X6, X7, X9, X10, X11, X13]:((((r2_hidden(esk1_3(X5,X6,X7),k1_relat_1(X5))|~r2_hidden(X7,X6)|X6!=k2_relat_1(X5)|(~v1_relat_1(X5)|~v1_funct_1(X5)))&(X7=k1_funct_1(X5,esk1_3(X5,X6,X7))|~r2_hidden(X7,X6)|X6!=k2_relat_1(X5)|(~v1_relat_1(X5)|~v1_funct_1(X5))))&(~r2_hidden(X10,k1_relat_1(X5))|X9!=k1_funct_1(X5,X10)|r2_hidden(X9,X6)|X6!=k2_relat_1(X5)|(~v1_relat_1(X5)|~v1_funct_1(X5))))&((~r2_hidden(esk2_2(X5,X11),X11)|(~r2_hidden(X13,k1_relat_1(X5))|esk2_2(X5,X11)!=k1_funct_1(X5,X13))|X11=k2_relat_1(X5)|(~v1_relat_1(X5)|~v1_funct_1(X5)))&((r2_hidden(esk3_2(X5,X11),k1_relat_1(X5))|r2_hidden(esk2_2(X5,X11),X11)|X11=k2_relat_1(X5)|(~v1_relat_1(X5)|~v1_funct_1(X5)))&(esk2_2(X5,X11)=k1_funct_1(X5,esk3_2(X5,X11))|r2_hidden(esk2_2(X5,X11),X11)|X11=k2_relat_1(X5)|(~v1_relat_1(X5)|~v1_funct_1(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X21, X22]:((r2_hidden(esk4_2(X21,X22),k1_relat_1(X21))|k1_relat_1(X21)!=k1_relat_1(X22)|X21=X22|(~v1_relat_1(X22)|~v1_funct_1(X22))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(k1_funct_1(X21,esk4_2(X21,X22))!=k1_funct_1(X22,esk4_2(X21,X22))|k1_relat_1(X21)!=k1_relat_1(X22)|X21=X22|(~v1_relat_1(X22)|~v1_funct_1(X22))|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&((((esk5_0=k2_relat_1(esk6_0)&k1_relat_1(esk7_0)=esk5_0)&k1_relat_1(esk8_0)=esk5_0)&k5_relat_1(esk6_0,esk7_0)=k5_relat_1(esk6_0,esk8_0))&esk7_0!=esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.12/0.37  cnf(c_0_9, plain, (X1=k1_funct_1(X2,esk1_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_10, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_14, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_15, plain, (k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2))=X2|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (esk5_0=k2_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (X1=esk8_0|r2_hidden(esk4_2(X1,esk8_0),k1_relat_1(X1))|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12]), c_0_13])])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (esk7_0!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_24, plain, (r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_14])).
% 0.12/0.37  fof(c_0_25, plain, ![X15, X16, X17]:(((r2_hidden(X15,k1_relat_1(X17))|~r2_hidden(X15,k1_relat_1(k5_relat_1(X17,X16)))|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(r2_hidden(k1_funct_1(X17,X15),k1_relat_1(X16))|~r2_hidden(X15,k1_relat_1(k5_relat_1(X17,X16)))|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(~r2_hidden(X15,k1_relat_1(X17))|~r2_hidden(k1_funct_1(X17,X15),k1_relat_1(X16))|r2_hidden(X15,k1_relat_1(k5_relat_1(X17,X16)))|(~v1_relat_1(X17)|~v1_funct_1(X17))|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (k1_funct_1(esk6_0,esk1_3(esk6_0,esk5_0,X1))=X1|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_2(esk7_0,esk8_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_3(esk6_0,esk5_0,X1),k1_relat_1(esk6_0))|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_16]), c_0_17]), c_0_18])])).
% 0.12/0.37  cnf(c_0_29, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk6_0,esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0)))=esk4_2(esk7_0,esk8_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0)),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_27])).
% 0.12/0.37  fof(c_0_32, plain, ![X18, X19, X20]:(~v1_relat_1(X19)|~v1_funct_1(X19)|(~v1_relat_1(X20)|~v1_funct_1(X20)|(~r2_hidden(X18,k1_relat_1(k5_relat_1(X20,X19)))|k1_funct_1(k5_relat_1(X20,X19),X18)=k1_funct_1(X19,k1_funct_1(X20,X18))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0)),k1_relat_1(k5_relat_1(esk6_0,X1)))|~r2_hidden(esk4_2(esk7_0,esk8_0),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_17]), c_0_18])])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k5_relat_1(esk6_0,esk7_0)=k5_relat_1(esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_35, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0)),k1_relat_1(k5_relat_1(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_12]), c_0_34]), c_0_27]), c_0_11]), c_0_13])])).
% 0.12/0.37  cnf(c_0_37, plain, (X1=X2|k1_funct_1(X1,esk4_2(X1,X2))!=k1_funct_1(X2,esk4_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,esk7_0),X1)=k1_funct_1(esk8_0,k1_funct_1(esk6_0,X1))|~r2_hidden(X1,k1_relat_1(k5_relat_1(esk6_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_34]), c_0_17]), c_0_11]), c_0_18]), c_0_13])])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,esk7_0),esk1_3(esk6_0,esk5_0,esk4_2(esk7_0,esk8_0)))=k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_30]), c_0_17]), c_0_21]), c_0_18]), c_0_22])])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (X1=esk8_0|k1_funct_1(X1,esk4_2(X1,esk8_0))!=k1_funct_1(esk8_0,esk4_2(X1,esk8_0))|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_11]), c_0_12]), c_0_13])])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (k1_funct_1(esk8_0,esk4_2(esk7_0,esk8_0))=k1_funct_1(esk7_0,esk4_2(esk7_0,esk8_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_36]), c_0_30]), c_0_39])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 43
% 0.12/0.37  # Proof object clause steps            : 32
% 0.12/0.37  # Proof object formula steps           : 11
% 0.12/0.37  # Proof object conjectures             : 27
% 0.12/0.37  # Proof object clause conjectures      : 24
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 17
% 0.12/0.37  # Proof object initial formulas used   : 5
% 0.12/0.37  # Proof object generating inferences   : 13
% 0.12/0.37  # Proof object simplifying inferences  : 45
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 5
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 23
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 23
% 0.12/0.37  # Processed clauses                    : 95
% 0.12/0.37  # ...of these trivial                  : 5
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 90
% 0.12/0.37  # Other redundant clauses eliminated   : 4
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 4
% 0.12/0.37  # Generated clauses                    : 101
% 0.12/0.37  # ...of the previous two non-trivial   : 92
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 94
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 8
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
% 0.12/0.37  # Current number of processed clauses  : 60
% 0.12/0.37  #    Positive orientable unit clauses  : 27
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 32
% 0.12/0.37  # Current number of unprocessed clauses: 39
% 0.12/0.37  # ...number of literals in the above   : 107
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 27
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 69
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 27
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 73
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 17
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4684
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.029 s
% 0.12/0.37  # System time              : 0.008 s
% 0.12/0.37  # Total time               : 0.037 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
