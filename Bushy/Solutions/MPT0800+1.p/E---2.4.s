%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : wellord1__t52_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:14 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   29 (  59 expanded)
%              Number of clauses        :   18 (  21 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :  154 ( 400 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r4_wellord1(X1,X2)
          <=> ? [X3] :
                ( v1_relat_1(X3)
                & v1_funct_1(X3)
                & r3_wellord1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',d8_wellord1)).

fof(t51_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ! [X4] :
                  ( ( v1_relat_1(X4)
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( ( v1_relat_1(X5)
                        & v1_funct_1(X5) )
                     => ( ( r3_wellord1(X1,X2,X4)
                          & r3_wellord1(X2,X3,X5) )
                       => r3_wellord1(X1,X3,k5_relat_1(X4,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',t51_wellord1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',dt_k5_relat_1)).

fof(fc2_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v1_relat_1(k5_relat_1(X1,X2))
        & v1_funct_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',fc2_funct_1)).

fof(t52_wellord1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X2,X3) )
               => r4_wellord1(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord1__t52_wellord1.p',t52_wellord1)).

fof(c_0_5,plain,(
    ! [X9,X10,X12] :
      ( ( v1_relat_1(esk4_2(X9,X10))
        | ~ r4_wellord1(X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9) )
      & ( v1_funct_1(esk4_2(X9,X10))
        | ~ r4_wellord1(X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9) )
      & ( r3_wellord1(X9,X10,esk4_2(X9,X10))
        | ~ r4_wellord1(X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9) )
      & ( ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ r3_wellord1(X9,X10,X12)
        | r4_wellord1(X9,X10)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_wellord1])])])])])).

fof(c_0_6,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | ~ v1_relat_1(X17)
      | ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ r3_wellord1(X15,X16,X18)
      | ~ r3_wellord1(X16,X17,X19)
      | r3_wellord1(X15,X17,k5_relat_1(X18,X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_wellord1])])])).

fof(c_0_7,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | v1_relat_1(k5_relat_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_8,plain,(
    ! [X20,X21] :
      ( ( v1_relat_1(k5_relat_1(X20,X21))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k5_relat_1(X20,X21))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_funct_1])])])).

cnf(c_0_9,plain,
    ( r4_wellord1(X2,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r3_wellord1(X2,X3,X1)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( r3_wellord1(X1,X3,k5_relat_1(X4,X5))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ v1_relat_1(X5)
    | ~ v1_funct_1(X5)
    | ~ r3_wellord1(X1,X2,X4)
    | ~ r3_wellord1(X2,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( ( r4_wellord1(X1,X2)
                    & r4_wellord1(X2,X3) )
                 => r4_wellord1(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_wellord1])).

cnf(c_0_14,plain,
    ( r4_wellord1(X1,X2)
    | ~ r3_wellord1(X3,X2,X4)
    | ~ r3_wellord1(X1,X3,X5)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_15,plain,
    ( r3_wellord1(X1,X2,esk4_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,plain,
    ( v1_relat_1(esk4_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( v1_funct_1(esk4_2(X1,X2))
    | ~ r4_wellord1(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_18,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & r4_wellord1(esk1_0,esk2_0)
    & r4_wellord1(esk2_0,esk3_0)
    & ~ r4_wellord1(esk1_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_19,plain,
    ( r4_wellord1(X1,X2)
    | ~ r3_wellord1(X3,X2,X4)
    | ~ v1_funct_1(X4)
    | ~ r4_wellord1(X1,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( ~ r4_wellord1(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( r4_wellord1(X1,X2)
    | ~ r4_wellord1(X1,X3)
    | ~ r4_wellord1(X3,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ r4_wellord1(esk1_0,X1)
    | ~ r4_wellord1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])])).

cnf(c_0_25,negated_conjecture,
    ( r4_wellord1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r4_wellord1(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
