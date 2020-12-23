%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:45 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 160 expanded)
%              Number of clauses        :   26 (  55 expanded)
%              Number of leaves         :    7 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  278 ( 989 expanded)
%              Number of equality atoms :   79 ( 280 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t54_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( X2 = k2_funct_1(X1)
            <=> ( k1_relat_1(X2) = k2_relat_1(X1)
                & ! [X3,X4] :
                    ( ( ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) )
                     => ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) ) )
                    & ( ( r2_hidden(X4,k1_relat_1(X1))
                        & X3 = k1_funct_1(X1,X4) )
                     => ( r2_hidden(X3,k2_relat_1(X1))
                        & X4 = k1_funct_1(X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(t22_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
           => k1_funct_1(k5_relat_1(X3,X2),X1) = k1_funct_1(X2,k1_funct_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_8,plain,(
    ! [X27] :
      ( ( k2_relat_1(X27) = k1_relat_1(k2_funct_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( k1_relat_1(X27) = k2_relat_1(k2_funct_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v2_funct_1(esk7_0)
    & r2_hidden(esk6_0,k2_relat_1(esk7_0))
    & ( esk6_0 != k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))
      | esk6_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X13] :
      ( ( v1_relat_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( v1_funct_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_11,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r1_tarski(k2_relat_1(X11),k1_relat_1(X12))
      | k1_relat_1(k5_relat_1(X11,X12)) = k1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_12,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( k1_relat_1(X18) = k2_relat_1(X17)
        | X18 != k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(X20,k1_relat_1(X17))
        | ~ r2_hidden(X19,k2_relat_1(X17))
        | X20 != k1_funct_1(X18,X19)
        | X18 != k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( X19 = k1_funct_1(X17,X20)
        | ~ r2_hidden(X19,k2_relat_1(X17))
        | X20 != k1_funct_1(X18,X19)
        | X18 != k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(X21,k2_relat_1(X17))
        | ~ r2_hidden(X22,k1_relat_1(X17))
        | X21 != k1_funct_1(X17,X22)
        | X18 != k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( X22 = k1_funct_1(X18,X21)
        | ~ r2_hidden(X22,k1_relat_1(X17))
        | X21 != k1_funct_1(X17,X22)
        | X18 != k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk5_2(X17,X18),k1_relat_1(X17))
        | r2_hidden(esk2_2(X17,X18),k2_relat_1(X17))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk4_2(X17,X18) = k1_funct_1(X17,esk5_2(X17,X18))
        | r2_hidden(esk2_2(X17,X18),k2_relat_1(X17))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(esk4_2(X17,X18),k2_relat_1(X17))
        | esk5_2(X17,X18) != k1_funct_1(X18,esk4_2(X17,X18))
        | r2_hidden(esk2_2(X17,X18),k2_relat_1(X17))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk5_2(X17,X18),k1_relat_1(X17))
        | esk3_2(X17,X18) = k1_funct_1(X18,esk2_2(X17,X18))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk4_2(X17,X18) = k1_funct_1(X17,esk5_2(X17,X18))
        | esk3_2(X17,X18) = k1_funct_1(X18,esk2_2(X17,X18))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(esk4_2(X17,X18),k2_relat_1(X17))
        | esk5_2(X17,X18) != k1_funct_1(X18,esk4_2(X17,X18))
        | esk3_2(X17,X18) = k1_funct_1(X18,esk2_2(X17,X18))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk5_2(X17,X18),k1_relat_1(X17))
        | ~ r2_hidden(esk3_2(X17,X18),k1_relat_1(X17))
        | esk2_2(X17,X18) != k1_funct_1(X17,esk3_2(X17,X18))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk4_2(X17,X18) = k1_funct_1(X17,esk5_2(X17,X18))
        | ~ r2_hidden(esk3_2(X17,X18),k1_relat_1(X17))
        | esk2_2(X17,X18) != k1_funct_1(X17,esk3_2(X17,X18))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(esk4_2(X17,X18),k2_relat_1(X17))
        | esk5_2(X17,X18) != k1_funct_1(X18,esk4_2(X17,X18))
        | ~ r2_hidden(esk3_2(X17,X18),k1_relat_1(X17))
        | esk2_2(X17,X18) != k1_funct_1(X17,esk3_2(X17,X18))
        | k1_relat_1(X18) != k2_relat_1(X17)
        | X18 = k2_funct_1(X17)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18)
        | ~ v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

cnf(c_0_20,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk7_0)) = k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_15])])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk7_0)) = k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | X3 != k1_funct_1(X4,X1)
    | X4 != k2_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_28,plain,(
    ! [X14,X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ v1_relat_1(X16)
      | ~ v1_funct_1(X16)
      | ~ r2_hidden(X14,k1_relat_1(k5_relat_1(X16,X15)))
      | k1_funct_1(k5_relat_1(X16,X15),X14) = k1_funct_1(X15,k1_funct_1(X16,X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk7_0),X1)) = k2_relat_1(esk7_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(esk7_0),k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X2)) = X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])]),c_0_16]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0)) = k2_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13]),c_0_15])])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 != k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))
    | esk6_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0)) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14]),c_0_13]),c_0_15])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),X1) = k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),X1))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_13]),c_0_22]),c_0_15])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_37]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.14/0.39  # and selection function SelectGrCQArEqFirst.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.029 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 0.14/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.14/0.39  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.14/0.39  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 0.14/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.39  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 0.14/0.39  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 0.14/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 0.14/0.39  fof(c_0_8, plain, ![X27]:((k2_relat_1(X27)=k1_relat_1(k2_funct_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(k1_relat_1(X27)=k2_relat_1(k2_funct_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.14/0.39  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((v2_funct_1(esk7_0)&r2_hidden(esk6_0,k2_relat_1(esk7_0)))&(esk6_0!=k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))|esk6_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.14/0.39  fof(c_0_10, plain, ![X13]:((v1_relat_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(v1_funct_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.14/0.39  fof(c_0_11, plain, ![X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|(~r1_tarski(k2_relat_1(X11),k1_relat_1(X12))|k1_relat_1(k5_relat_1(X11,X12))=k1_relat_1(X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.14/0.39  cnf(c_0_12, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_14, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_16, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_17, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.39  fof(c_0_18, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.39  fof(c_0_19, plain, ![X17, X18, X19, X20, X21, X22]:(((k1_relat_1(X18)=k2_relat_1(X17)|X18!=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(((r2_hidden(X20,k1_relat_1(X17))|(~r2_hidden(X19,k2_relat_1(X17))|X20!=k1_funct_1(X18,X19))|X18!=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(X19=k1_funct_1(X17,X20)|(~r2_hidden(X19,k2_relat_1(X17))|X20!=k1_funct_1(X18,X19))|X18!=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&((r2_hidden(X21,k2_relat_1(X17))|(~r2_hidden(X22,k1_relat_1(X17))|X21!=k1_funct_1(X17,X22))|X18!=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(X22=k1_funct_1(X18,X21)|(~r2_hidden(X22,k1_relat_1(X17))|X21!=k1_funct_1(X17,X22))|X18!=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))))&(((((r2_hidden(esk5_2(X17,X18),k1_relat_1(X17))|r2_hidden(esk2_2(X17,X18),k2_relat_1(X17))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(esk4_2(X17,X18)=k1_funct_1(X17,esk5_2(X17,X18))|r2_hidden(esk2_2(X17,X18),k2_relat_1(X17))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(esk4_2(X17,X18),k2_relat_1(X17))|esk5_2(X17,X18)!=k1_funct_1(X18,esk4_2(X17,X18))|r2_hidden(esk2_2(X17,X18),k2_relat_1(X17))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(((r2_hidden(esk5_2(X17,X18),k1_relat_1(X17))|esk3_2(X17,X18)=k1_funct_1(X18,esk2_2(X17,X18))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(esk4_2(X17,X18)=k1_funct_1(X17,esk5_2(X17,X18))|esk3_2(X17,X18)=k1_funct_1(X18,esk2_2(X17,X18))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(esk4_2(X17,X18),k2_relat_1(X17))|esk5_2(X17,X18)!=k1_funct_1(X18,esk4_2(X17,X18))|esk3_2(X17,X18)=k1_funct_1(X18,esk2_2(X17,X18))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))))&(((r2_hidden(esk5_2(X17,X18),k1_relat_1(X17))|(~r2_hidden(esk3_2(X17,X18),k1_relat_1(X17))|esk2_2(X17,X18)!=k1_funct_1(X17,esk3_2(X17,X18)))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(esk4_2(X17,X18)=k1_funct_1(X17,esk5_2(X17,X18))|(~r2_hidden(esk3_2(X17,X18),k1_relat_1(X17))|esk2_2(X17,X18)!=k1_funct_1(X17,esk3_2(X17,X18)))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(esk4_2(X17,X18),k2_relat_1(X17))|esk5_2(X17,X18)!=k1_funct_1(X18,esk4_2(X17,X18))|(~r2_hidden(esk3_2(X17,X18),k1_relat_1(X17))|esk2_2(X17,X18)!=k1_funct_1(X17,esk3_2(X17,X18)))|k1_relat_1(X18)!=k2_relat_1(X17)|X18=k2_funct_1(X17)|(~v1_relat_1(X18)|~v1_funct_1(X18))|~v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.14/0.39  cnf(c_0_20, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_21, negated_conjecture, (k2_relat_1(k2_funct_1(esk7_0))=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_13]), c_0_15])])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, (k1_relat_1(k2_funct_1(esk7_0))=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_13]), c_0_14]), c_0_15])])).
% 0.14/0.39  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_26, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(X1,k2_relat_1(X2))|X3!=k1_funct_1(X4,X1)|X4!=k2_funct_1(X2)|~v1_relat_1(X4)|~v1_funct_1(X4)|~v2_funct_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_27, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  fof(c_0_28, plain, ![X14, X15, X16]:(~v1_relat_1(X15)|~v1_funct_1(X15)|(~v1_relat_1(X16)|~v1_funct_1(X16)|(~r2_hidden(X14,k1_relat_1(k5_relat_1(X16,X15)))|k1_funct_1(k5_relat_1(X16,X15),X14)=k1_funct_1(X15,k1_funct_1(X16,X14))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk7_0),X1))=k2_relat_1(esk7_0)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(esk7_0),k1_relat_1(X1))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])]), c_0_23])).
% 0.14/0.39  cnf(c_0_30, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.39  cnf(c_0_31, plain, (k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X2))=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])]), c_0_16]), c_0_27])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_33, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0))=k2_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_15])])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (v1_funct_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_13]), c_0_15])])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (esk6_0!=k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))|esk6_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_14]), c_0_13]), c_0_15])])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),X1)=k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),X1))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_13]), c_0_22]), c_0_15])])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_32]), c_0_37]), c_0_39]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 41
% 0.14/0.39  # Proof object clause steps            : 26
% 0.14/0.39  # Proof object formula steps           : 15
% 0.14/0.39  # Proof object conjectures             : 18
% 0.14/0.39  # Proof object clause conjectures      : 15
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 14
% 0.14/0.39  # Proof object initial formulas used   : 7
% 0.14/0.39  # Proof object generating inferences   : 10
% 0.14/0.39  # Proof object simplifying inferences  : 32
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 7
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 28
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 28
% 0.14/0.39  # Processed clauses                    : 108
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 2
% 0.14/0.39  # ...remaining for further processing  : 106
% 0.14/0.39  # Other redundant clauses eliminated   : 9
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 1
% 0.14/0.39  # Generated clauses                    : 141
% 0.14/0.39  # ...of the previous two non-trivial   : 137
% 0.14/0.39  # Contextual simplify-reflections      : 8
% 0.14/0.39  # Paramodulations                      : 136
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 9
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 73
% 0.14/0.39  #    Positive orientable unit clauses  : 35
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 1
% 0.14/0.39  #    Non-unit-clauses                  : 37
% 0.14/0.39  # Current number of unprocessed clauses: 84
% 0.14/0.39  # ...number of literals in the above   : 462
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 28
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1253
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 77
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 10
% 0.14/0.39  # Unit Clause-clause subsumption calls : 260
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 114
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 8439
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.039 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.042 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
