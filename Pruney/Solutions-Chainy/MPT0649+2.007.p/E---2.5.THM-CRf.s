%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 161 expanded)
%              Number of clauses        :   27 (  57 expanded)
%              Number of leaves         :    7 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  267 (1107 expanded)
%              Number of equality atoms :   79 ( 318 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t56_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t46_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(X2))
           => k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

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

fof(c_0_7,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( k1_relat_1(X15) = k2_relat_1(X14)
        | X15 != k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(X17,k1_relat_1(X14))
        | ~ r2_hidden(X16,k2_relat_1(X14))
        | X17 != k1_funct_1(X15,X16)
        | X15 != k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( X16 = k1_funct_1(X14,X17)
        | ~ r2_hidden(X16,k2_relat_1(X14))
        | X17 != k1_funct_1(X15,X16)
        | X15 != k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(X18,k2_relat_1(X14))
        | ~ r2_hidden(X19,k1_relat_1(X14))
        | X18 != k1_funct_1(X14,X19)
        | X15 != k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( X19 = k1_funct_1(X15,X18)
        | ~ r2_hidden(X19,k1_relat_1(X14))
        | X18 != k1_funct_1(X14,X19)
        | X15 != k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(esk4_2(X14,X15),k1_relat_1(X14))
        | r2_hidden(esk1_2(X14,X15),k2_relat_1(X14))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( esk3_2(X14,X15) = k1_funct_1(X14,esk4_2(X14,X15))
        | r2_hidden(esk1_2(X14,X15),k2_relat_1(X14))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(esk3_2(X14,X15),k2_relat_1(X14))
        | esk4_2(X14,X15) != k1_funct_1(X15,esk3_2(X14,X15))
        | r2_hidden(esk1_2(X14,X15),k2_relat_1(X14))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(esk4_2(X14,X15),k1_relat_1(X14))
        | esk2_2(X14,X15) = k1_funct_1(X15,esk1_2(X14,X15))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( esk3_2(X14,X15) = k1_funct_1(X14,esk4_2(X14,X15))
        | esk2_2(X14,X15) = k1_funct_1(X15,esk1_2(X14,X15))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(esk3_2(X14,X15),k2_relat_1(X14))
        | esk4_2(X14,X15) != k1_funct_1(X15,esk3_2(X14,X15))
        | esk2_2(X14,X15) = k1_funct_1(X15,esk1_2(X14,X15))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( r2_hidden(esk4_2(X14,X15),k1_relat_1(X14))
        | ~ r2_hidden(esk2_2(X14,X15),k1_relat_1(X14))
        | esk1_2(X14,X15) != k1_funct_1(X14,esk2_2(X14,X15))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( esk3_2(X14,X15) = k1_funct_1(X14,esk4_2(X14,X15))
        | ~ r2_hidden(esk2_2(X14,X15),k1_relat_1(X14))
        | esk1_2(X14,X15) != k1_funct_1(X14,esk2_2(X14,X15))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( ~ r2_hidden(esk3_2(X14,X15),k2_relat_1(X14))
        | esk4_2(X14,X15) != k1_funct_1(X15,esk3_2(X14,X15))
        | ~ r2_hidden(esk2_2(X14,X15),k1_relat_1(X14))
        | esk1_2(X14,X15) != k1_funct_1(X14,esk2_2(X14,X15))
        | k1_relat_1(X15) != k2_relat_1(X14)
        | X15 = k2_funct_1(X14)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15)
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_8,plain,(
    ! [X10] :
      ( ( v1_relat_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k1_relat_1(X2)) )
         => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
            & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_funct_1])).

cnf(c_0_10,plain,
    ( k1_relat_1(X1) = k2_relat_1(X2)
    | X1 != k2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v2_funct_1(esk6_0)
    & r2_hidden(esk5_0,k1_relat_1(esk6_0))
    & ( esk5_0 != k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))
      | esk5_0 != k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | r1_tarski(k2_relat_1(k7_relat_1(X9,X8)),k2_relat_1(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

fof(c_0_15,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k7_relat_1(X7,k1_relat_1(X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(k2_relat_1(X5),k1_relat_1(X6))
      | k1_relat_1(k5_relat_1(X5,X6)) = k1_relat_1(X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_17,plain,
    ( k1_relat_1(k2_funct_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk6_0)) = k2_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_18]),c_0_20])])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk6_0,X1)),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_relat_1(esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_28,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(X1,k1_relat_1(X4))
    | X3 != k1_funct_1(X4,X1)
    | X2 != k2_funct_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X4)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_29,plain,(
    ! [X11,X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ r2_hidden(X11,k1_relat_1(k5_relat_1(X13,X12)))
      | k1_funct_1(k5_relat_1(X13,X12),X11) = k1_funct_1(X12,k1_funct_1(X13,X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(esk6_0))) = k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k2_relat_1(esk6_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2)) = X2
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])]),c_0_11]),c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0))) = k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_20])])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_18]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 != k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))
    | esk5_0 != k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_19]),c_0_18]),c_0_20])])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),X1) = k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_18]),c_0_36]),c_0_20]),c_0_25])])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_38]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.19/0.37  # and selection function SelectGrCQArEqFirst.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 0.19/0.37  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.37  fof(t56_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 0.19/0.37  fof(t99_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 0.19/0.37  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.19/0.37  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 0.19/0.37  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.19/0.37  fof(c_0_7, plain, ![X14, X15, X16, X17, X18, X19]:(((k1_relat_1(X15)=k2_relat_1(X14)|X15!=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(((r2_hidden(X17,k1_relat_1(X14))|(~r2_hidden(X16,k2_relat_1(X14))|X17!=k1_funct_1(X15,X16))|X15!=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(X16=k1_funct_1(X14,X17)|(~r2_hidden(X16,k2_relat_1(X14))|X17!=k1_funct_1(X15,X16))|X15!=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&((r2_hidden(X18,k2_relat_1(X14))|(~r2_hidden(X19,k1_relat_1(X14))|X18!=k1_funct_1(X14,X19))|X15!=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(X19=k1_funct_1(X15,X18)|(~r2_hidden(X19,k1_relat_1(X14))|X18!=k1_funct_1(X14,X19))|X15!=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))))&(((((r2_hidden(esk4_2(X14,X15),k1_relat_1(X14))|r2_hidden(esk1_2(X14,X15),k2_relat_1(X14))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(esk3_2(X14,X15)=k1_funct_1(X14,esk4_2(X14,X15))|r2_hidden(esk1_2(X14,X15),k2_relat_1(X14))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(esk3_2(X14,X15),k2_relat_1(X14))|esk4_2(X14,X15)!=k1_funct_1(X15,esk3_2(X14,X15))|r2_hidden(esk1_2(X14,X15),k2_relat_1(X14))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(((r2_hidden(esk4_2(X14,X15),k1_relat_1(X14))|esk2_2(X14,X15)=k1_funct_1(X15,esk1_2(X14,X15))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(esk3_2(X14,X15)=k1_funct_1(X14,esk4_2(X14,X15))|esk2_2(X14,X15)=k1_funct_1(X15,esk1_2(X14,X15))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(esk3_2(X14,X15),k2_relat_1(X14))|esk4_2(X14,X15)!=k1_funct_1(X15,esk3_2(X14,X15))|esk2_2(X14,X15)=k1_funct_1(X15,esk1_2(X14,X15))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))))&(((r2_hidden(esk4_2(X14,X15),k1_relat_1(X14))|(~r2_hidden(esk2_2(X14,X15),k1_relat_1(X14))|esk1_2(X14,X15)!=k1_funct_1(X14,esk2_2(X14,X15)))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(esk3_2(X14,X15)=k1_funct_1(X14,esk4_2(X14,X15))|(~r2_hidden(esk2_2(X14,X15),k1_relat_1(X14))|esk1_2(X14,X15)!=k1_funct_1(X14,esk2_2(X14,X15)))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14))))&(~r2_hidden(esk3_2(X14,X15),k2_relat_1(X14))|esk4_2(X14,X15)!=k1_funct_1(X15,esk3_2(X14,X15))|(~r2_hidden(esk2_2(X14,X15),k1_relat_1(X14))|esk1_2(X14,X15)!=k1_funct_1(X14,esk2_2(X14,X15)))|k1_relat_1(X15)!=k2_relat_1(X14)|X15=k2_funct_1(X14)|(~v1_relat_1(X15)|~v1_funct_1(X15))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.19/0.37  fof(c_0_8, plain, ![X10]:((v1_relat_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(v1_funct_1(k2_funct_1(X10))|(~v1_relat_1(X10)|~v1_funct_1(X10)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.37  fof(c_0_9, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1))))), inference(assume_negation,[status(cth)],[t56_funct_1])).
% 0.19/0.37  cnf(c_0_10, plain, (k1_relat_1(X1)=k2_relat_1(X2)|X1!=k2_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  cnf(c_0_11, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  cnf(c_0_12, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.37  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v2_funct_1(esk6_0)&r2_hidden(esk5_0,k1_relat_1(esk6_0)))&(esk5_0!=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X8, X9]:(~v1_relat_1(X9)|r1_tarski(k2_relat_1(k7_relat_1(X9,X8)),k2_relat_1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).
% 0.19/0.37  fof(c_0_15, plain, ![X7]:(~v1_relat_1(X7)|k7_relat_1(X7,k1_relat_1(X7))=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.19/0.37  fof(c_0_16, plain, ![X5, X6]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|(~r1_tarski(k2_relat_1(X5),k1_relat_1(X6))|k1_relat_1(k5_relat_1(X5,X6))=k1_relat_1(X5)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.19/0.37  cnf(c_0_17, plain, (k1_relat_1(k2_funct_1(X1))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11]), c_0_12])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_21, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_22, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_23, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (k1_relat_1(k2_funct_1(esk6_0))=k2_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_18]), c_0_20])])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk6_0,X1)),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (k7_relat_1(esk6_0,k1_relat_1(esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.19/0.37  cnf(c_0_28, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(X1,k1_relat_1(X4))|X3!=k1_funct_1(X4,X1)|X2!=k2_funct_1(X4)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X4)|~v1_relat_1(X4)|~v1_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.37  fof(c_0_29, plain, ![X11, X12, X13]:(~v1_relat_1(X12)|~v1_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13)|(~r2_hidden(X11,k1_relat_1(k5_relat_1(X13,X12)))|k1_funct_1(k5_relat_1(X13,X12),X11)=k1_funct_1(X12,k1_funct_1(X13,X11))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k1_relat_1(k5_relat_1(X1,k2_funct_1(esk6_0)))=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k2_relat_1(esk6_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.37  cnf(c_0_32, plain, (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2))=X2|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])]), c_0_11]), c_0_12])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_34, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (k1_relat_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)))=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_20])])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_18]), c_0_20])])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (esk5_0!=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_19]), c_0_18]), c_0_20])])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),X1)=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_18]), c_0_36]), c_0_20]), c_0_25])])).
% 0.19/0.37  cnf(c_0_40, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_33]), c_0_38]), c_0_40]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 42
% 0.19/0.37  # Proof object clause steps            : 27
% 0.19/0.37  # Proof object formula steps           : 15
% 0.19/0.37  # Proof object conjectures             : 20
% 0.19/0.37  # Proof object clause conjectures      : 17
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 13
% 0.19/0.37  # Proof object initial formulas used   : 7
% 0.19/0.37  # Proof object generating inferences   : 11
% 0.19/0.37  # Proof object simplifying inferences  : 31
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 7
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 25
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 25
% 0.19/0.37  # Processed clauses                    : 88
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 88
% 0.19/0.37  # Other redundant clauses eliminated   : 9
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 1
% 0.19/0.37  # Generated clauses                    : 89
% 0.19/0.37  # ...of the previous two non-trivial   : 86
% 0.19/0.37  # Contextual simplify-reflections      : 10
% 0.19/0.37  # Paramodulations                      : 84
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 9
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 57
% 0.19/0.37  #    Positive orientable unit clauses  : 31
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 25
% 0.19/0.37  # Current number of unprocessed clauses: 48
% 0.19/0.37  # ...number of literals in the above   : 208
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 26
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 778
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 32
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 10
% 0.19/0.37  # Unit Clause-clause subsumption calls : 188
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 57
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 5556
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.034 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.038 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
