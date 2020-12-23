%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:44 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 141 expanded)
%              Number of clauses        :   23 (  49 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  271 ( 902 expanded)
%              Number of equality atoms :   82 ( 261 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t56_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
            & r2_hidden(X1,k1_relat_1(X2)) )
         => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
            & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t56_funct_1])).

fof(c_0_8,plain,(
    ! [X23] :
      ( ( k2_relat_1(X23) = k1_relat_1(k2_funct_1(X23))
        | ~ v2_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( k1_relat_1(X23) = k2_relat_1(k2_funct_1(X23))
        | ~ v2_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v2_funct_1(esk6_0)
    & r2_hidden(esk5_0,k1_relat_1(esk6_0))
    & ( esk5_0 != k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))
      | esk5_0 != k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X9] :
      ( ( v1_relat_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( v1_funct_1(k2_funct_1(X9))
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | ~ r1_tarski(k2_relat_1(X7),k1_relat_1(X8))
      | k1_relat_1(k5_relat_1(X7,X8)) = k1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).

cnf(c_0_12,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( k1_relat_1(X14) = k2_relat_1(X13)
        | X14 != k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(X16,k1_relat_1(X13))
        | ~ r2_hidden(X15,k2_relat_1(X13))
        | X16 != k1_funct_1(X14,X15)
        | X14 != k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X15 = k1_funct_1(X13,X16)
        | ~ r2_hidden(X15,k2_relat_1(X13))
        | X16 != k1_funct_1(X14,X15)
        | X14 != k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(X17,k2_relat_1(X13))
        | ~ r2_hidden(X18,k1_relat_1(X13))
        | X17 != k1_funct_1(X13,X18)
        | X14 != k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( X18 = k1_funct_1(X14,X17)
        | ~ r2_hidden(X18,k1_relat_1(X13))
        | X17 != k1_funct_1(X13,X18)
        | X14 != k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk4_2(X13,X14),k1_relat_1(X13))
        | r2_hidden(esk1_2(X13,X14),k2_relat_1(X13))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( esk3_2(X13,X14) = k1_funct_1(X13,esk4_2(X13,X14))
        | r2_hidden(esk1_2(X13,X14),k2_relat_1(X13))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(esk3_2(X13,X14),k2_relat_1(X13))
        | esk4_2(X13,X14) != k1_funct_1(X14,esk3_2(X13,X14))
        | r2_hidden(esk1_2(X13,X14),k2_relat_1(X13))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk4_2(X13,X14),k1_relat_1(X13))
        | esk2_2(X13,X14) = k1_funct_1(X14,esk1_2(X13,X14))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( esk3_2(X13,X14) = k1_funct_1(X13,esk4_2(X13,X14))
        | esk2_2(X13,X14) = k1_funct_1(X14,esk1_2(X13,X14))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(esk3_2(X13,X14),k2_relat_1(X13))
        | esk4_2(X13,X14) != k1_funct_1(X14,esk3_2(X13,X14))
        | esk2_2(X13,X14) = k1_funct_1(X14,esk1_2(X13,X14))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( r2_hidden(esk4_2(X13,X14),k1_relat_1(X13))
        | ~ r2_hidden(esk2_2(X13,X14),k1_relat_1(X13))
        | esk1_2(X13,X14) != k1_funct_1(X13,esk2_2(X13,X14))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( esk3_2(X13,X14) = k1_funct_1(X13,esk4_2(X13,X14))
        | ~ r2_hidden(esk2_2(X13,X14),k1_relat_1(X13))
        | esk1_2(X13,X14) != k1_funct_1(X13,esk2_2(X13,X14))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( ~ r2_hidden(esk3_2(X13,X14),k2_relat_1(X13))
        | esk4_2(X13,X14) != k1_funct_1(X14,esk3_2(X13,X14))
        | ~ r2_hidden(esk2_2(X13,X14),k1_relat_1(X13))
        | esk1_2(X13,X14) != k1_funct_1(X13,esk2_2(X13,X14))
        | k1_relat_1(X14) != k2_relat_1(X13)
        | X14 = k2_funct_1(X13)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14)
        | ~ v2_funct_1(X13)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

cnf(c_0_19,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk6_0)) = k2_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_13]),c_0_15])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(X1,k1_relat_1(X4))
    | X3 != k1_funct_1(X4,X1)
    | X2 != k2_funct_1(X4)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X4)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_25,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ r2_hidden(X10,k1_relat_1(k5_relat_1(X12,X11)))
      | k1_funct_1(k5_relat_1(X12,X11),X10) = k1_funct_1(X11,k1_funct_1(X12,X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(esk6_0))) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2)) = X2
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])]),c_0_16]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0))) = k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_15])])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_13]),c_0_15])])).

cnf(c_0_33,negated_conjecture,
    ( esk5_0 != k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))
    | esk5_0 != k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14]),c_0_13]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),X1) = k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_13]),c_0_32]),c_0_15]),c_0_21])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_34]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:51:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.12/0.38  # and selection function SelectGrCQArEqFirst.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.028 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t56_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 0.12/0.38  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.12/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.12/0.38  fof(t46_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X1),k1_relat_1(X2))=>k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 0.12/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.38  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 0.12/0.38  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 0.12/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1))))), inference(assume_negation,[status(cth)],[t56_funct_1])).
% 0.12/0.38  fof(c_0_8, plain, ![X23]:((k2_relat_1(X23)=k1_relat_1(k2_funct_1(X23))|~v2_funct_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(k1_relat_1(X23)=k2_relat_1(k2_funct_1(X23))|~v2_funct_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.12/0.38  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v2_funct_1(esk6_0)&r2_hidden(esk5_0,k1_relat_1(esk6_0)))&(esk5_0!=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.12/0.38  fof(c_0_10, plain, ![X9]:((v1_relat_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(v1_funct_1(k2_funct_1(X9))|(~v1_relat_1(X9)|~v1_funct_1(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.12/0.38  fof(c_0_11, plain, ![X7, X8]:(~v1_relat_1(X7)|(~v1_relat_1(X8)|(~r1_tarski(k2_relat_1(X7),k1_relat_1(X8))|k1_relat_1(k5_relat_1(X7,X8))=k1_relat_1(X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_relat_1])])])).
% 0.12/0.38  cnf(c_0_12, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.38  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_14, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_16, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  fof(c_0_17, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.38  fof(c_0_18, plain, ![X13, X14, X15, X16, X17, X18]:(((k1_relat_1(X14)=k2_relat_1(X13)|X14!=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(((r2_hidden(X16,k1_relat_1(X13))|(~r2_hidden(X15,k2_relat_1(X13))|X16!=k1_funct_1(X14,X15))|X14!=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(X15=k1_funct_1(X13,X16)|(~r2_hidden(X15,k2_relat_1(X13))|X16!=k1_funct_1(X14,X15))|X14!=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&((r2_hidden(X17,k2_relat_1(X13))|(~r2_hidden(X18,k1_relat_1(X13))|X17!=k1_funct_1(X13,X18))|X14!=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(X18=k1_funct_1(X14,X17)|(~r2_hidden(X18,k1_relat_1(X13))|X17!=k1_funct_1(X13,X18))|X14!=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))))))&(((((r2_hidden(esk4_2(X13,X14),k1_relat_1(X13))|r2_hidden(esk1_2(X13,X14),k2_relat_1(X13))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(esk3_2(X13,X14)=k1_funct_1(X13,esk4_2(X13,X14))|r2_hidden(esk1_2(X13,X14),k2_relat_1(X13))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(esk3_2(X13,X14),k2_relat_1(X13))|esk4_2(X13,X14)!=k1_funct_1(X14,esk3_2(X13,X14))|r2_hidden(esk1_2(X13,X14),k2_relat_1(X13))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(((r2_hidden(esk4_2(X13,X14),k1_relat_1(X13))|esk2_2(X13,X14)=k1_funct_1(X14,esk1_2(X13,X14))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(esk3_2(X13,X14)=k1_funct_1(X13,esk4_2(X13,X14))|esk2_2(X13,X14)=k1_funct_1(X14,esk1_2(X13,X14))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(esk3_2(X13,X14),k2_relat_1(X13))|esk4_2(X13,X14)!=k1_funct_1(X14,esk3_2(X13,X14))|esk2_2(X13,X14)=k1_funct_1(X14,esk1_2(X13,X14))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))))&(((r2_hidden(esk4_2(X13,X14),k1_relat_1(X13))|(~r2_hidden(esk2_2(X13,X14),k1_relat_1(X13))|esk1_2(X13,X14)!=k1_funct_1(X13,esk2_2(X13,X14)))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(esk3_2(X13,X14)=k1_funct_1(X13,esk4_2(X13,X14))|(~r2_hidden(esk2_2(X13,X14),k1_relat_1(X13))|esk1_2(X13,X14)!=k1_funct_1(X13,esk2_2(X13,X14)))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13))))&(~r2_hidden(esk3_2(X13,X14),k2_relat_1(X13))|esk4_2(X13,X14)!=k1_funct_1(X14,esk3_2(X13,X14))|(~r2_hidden(esk2_2(X13,X14),k1_relat_1(X13))|esk1_2(X13,X14)!=k1_funct_1(X13,esk2_2(X13,X14)))|k1_relat_1(X14)!=k2_relat_1(X13)|X14=k2_funct_1(X13)|(~v1_relat_1(X14)|~v1_funct_1(X14))|~v2_funct_1(X13)|(~v1_relat_1(X13)|~v1_funct_1(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.12/0.38  cnf(c_0_19, plain, (k1_relat_1(k5_relat_1(X1,X2))=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X1),k1_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_20, negated_conjecture, (k1_relat_1(k2_funct_1(esk6_0))=k2_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15])])).
% 0.12/0.38  cnf(c_0_21, negated_conjecture, (v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_13]), c_0_15])])).
% 0.12/0.38  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  cnf(c_0_23, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(X1,k1_relat_1(X4))|X3!=k1_funct_1(X4,X1)|X2!=k2_funct_1(X4)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X4)|~v1_relat_1(X4)|~v1_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.38  cnf(c_0_24, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  fof(c_0_25, plain, ![X10, X11, X12]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~v1_relat_1(X12)|~v1_funct_1(X12)|(~r2_hidden(X10,k1_relat_1(k5_relat_1(X12,X11)))|k1_funct_1(k5_relat_1(X12,X11),X10)=k1_funct_1(X11,k1_funct_1(X12,X10))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.12/0.38  cnf(c_0_26, negated_conjecture, (k1_relat_1(k5_relat_1(X1,k2_funct_1(esk6_0)))=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.12/0.38  cnf(c_0_27, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_28, plain, (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2))=X2|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])]), c_0_16]), c_0_24])).
% 0.12/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_30, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_31, negated_conjecture, (k1_relat_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)))=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_15])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_13]), c_0_15])])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (esk5_0!=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_34, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_14]), c_0_13]), c_0_15])])).
% 0.12/0.38  cnf(c_0_35, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),X1)=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_13]), c_0_32]), c_0_15]), c_0_21])])).
% 0.12/0.38  cnf(c_0_36, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_34]), c_0_36]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 38
% 0.12/0.38  # Proof object clause steps            : 23
% 0.12/0.38  # Proof object formula steps           : 15
% 0.12/0.38  # Proof object conjectures             : 17
% 0.12/0.38  # Proof object clause conjectures      : 14
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 12
% 0.12/0.38  # Proof object initial formulas used   : 7
% 0.12/0.38  # Proof object generating inferences   : 8
% 0.12/0.38  # Proof object simplifying inferences  : 29
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 7
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 28
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 28
% 0.12/0.38  # Processed clauses                    : 107
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 2
% 0.12/0.38  # ...remaining for further processing  : 105
% 0.12/0.38  # Other redundant clauses eliminated   : 11
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 0
% 0.12/0.38  # Backward-rewritten                   : 1
% 0.12/0.38  # Generated clauses                    : 122
% 0.12/0.38  # ...of the previous two non-trivial   : 118
% 0.12/0.38  # Contextual simplify-reflections      : 8
% 0.12/0.38  # Paramodulations                      : 114
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 12
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 71
% 0.12/0.38  #    Positive orientable unit clauses  : 36
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 1
% 0.12/0.38  #    Non-unit-clauses                  : 34
% 0.12/0.38  # Current number of unprocessed clauses: 65
% 0.12/0.38  # ...number of literals in the above   : 386
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 27
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 970
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 63
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.12/0.38  # Unit Clause-clause subsumption calls : 134
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 122
% 0.12/0.38  # BW rewrite match successes           : 1
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 7406
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.036 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.040 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
