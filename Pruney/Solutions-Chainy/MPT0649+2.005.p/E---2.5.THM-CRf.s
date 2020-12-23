%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 145 expanded)
%              Number of clauses        :   23 (  50 expanded)
%              Number of leaves         :    7 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  261 ( 911 expanded)
%              Number of equality atoms :   81 ( 266 expanded)
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

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

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
    ! [X8] :
      ( ( v1_relat_1(k2_funct_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( v1_funct_1(k2_funct_1(X8))
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v2_funct_1(esk6_0)
    & r2_hidden(esk5_0,k1_relat_1(esk6_0))
    & ( esk5_0 != k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))
      | esk5_0 != k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X22] :
      ( ( k2_relat_1(X22) = k1_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_relat_1(X22) = k2_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_11,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | k1_relat_1(k5_relat_1(X6,X7)) = k10_relat_1(X6,k1_relat_1(X7)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_12,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_17,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k10_relat_1(X5,k2_relat_1(X5)) = k1_relat_1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

fof(c_0_18,plain,(
    ! [X12,X13,X14,X15,X16,X17] :
      ( ( k1_relat_1(X13) = k2_relat_1(X12)
        | X13 != k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(X15,k1_relat_1(X12))
        | ~ r2_hidden(X14,k2_relat_1(X12))
        | X15 != k1_funct_1(X13,X14)
        | X13 != k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X14 = k1_funct_1(X12,X15)
        | ~ r2_hidden(X14,k2_relat_1(X12))
        | X15 != k1_funct_1(X13,X14)
        | X13 != k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(X16,k2_relat_1(X12))
        | ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | X13 != k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( X17 = k1_funct_1(X13,X16)
        | ~ r2_hidden(X17,k1_relat_1(X12))
        | X16 != k1_funct_1(X12,X17)
        | X13 != k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X13),k1_relat_1(X12))
        | r2_hidden(esk1_2(X12,X13),k2_relat_1(X12))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X13) = k1_funct_1(X12,esk4_2(X12,X13))
        | r2_hidden(esk1_2(X12,X13),k2_relat_1(X12))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X13),k2_relat_1(X12))
        | esk4_2(X12,X13) != k1_funct_1(X13,esk3_2(X12,X13))
        | r2_hidden(esk1_2(X12,X13),k2_relat_1(X12))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X13),k1_relat_1(X12))
        | esk2_2(X12,X13) = k1_funct_1(X13,esk1_2(X12,X13))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X13) = k1_funct_1(X12,esk4_2(X12,X13))
        | esk2_2(X12,X13) = k1_funct_1(X13,esk1_2(X12,X13))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X13),k2_relat_1(X12))
        | esk4_2(X12,X13) != k1_funct_1(X13,esk3_2(X12,X13))
        | esk2_2(X12,X13) = k1_funct_1(X13,esk1_2(X12,X13))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( r2_hidden(esk4_2(X12,X13),k1_relat_1(X12))
        | ~ r2_hidden(esk2_2(X12,X13),k1_relat_1(X12))
        | esk1_2(X12,X13) != k1_funct_1(X12,esk2_2(X12,X13))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( esk3_2(X12,X13) = k1_funct_1(X12,esk4_2(X12,X13))
        | ~ r2_hidden(esk2_2(X12,X13),k1_relat_1(X12))
        | esk1_2(X12,X13) != k1_funct_1(X12,esk2_2(X12,X13))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( ~ r2_hidden(esk3_2(X12,X13),k2_relat_1(X12))
        | esk4_2(X12,X13) != k1_funct_1(X13,esk3_2(X12,X13))
        | ~ r2_hidden(esk2_2(X12,X13),k1_relat_1(X12))
        | esk1_2(X12,X13) != k1_funct_1(X12,esk2_2(X12,X13))
        | k1_relat_1(X13) != k2_relat_1(X12)
        | X13 = k2_funct_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

cnf(c_0_19,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk6_0)) = k2_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_16]),c_0_14])])).

cnf(c_0_22,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_25,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_funct_1(X10)
      | ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ r2_hidden(X9,k1_relat_1(k5_relat_1(X11,X10)))
      | k1_funct_1(k5_relat_1(X11,X10),X9) = k1_funct_1(X10,k1_funct_1(X11,X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_26,negated_conjecture,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(esk6_0))) = k10_relat_1(X1,k2_relat_1(esk6_0))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k10_relat_1(esk6_0,k2_relat_1(esk6_0)) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_28,plain,
    ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2)) = X2
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])]),c_0_12]),c_0_24])).

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
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_14]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_13]),c_0_14])])).

cnf(c_0_33,negated_conjecture,
    ( esk5_0 != k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))
    | esk5_0 != k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_16]),c_0_13]),c_0_14])])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),X1) = k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_13]),c_0_32]),c_0_14]),c_0_20])])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_34]),c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:30:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S2i
% 0.20/0.41  # and selection function SelectGrCQArEqFirst.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.042 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t56_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 0.20/0.41  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.41  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.41  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.41  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 0.20/0.41  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_funct_1)).
% 0.20/0.41  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_funct_1)).
% 0.20/0.41  fof(c_0_7, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1))))), inference(assume_negation,[status(cth)],[t56_funct_1])).
% 0.20/0.41  fof(c_0_8, plain, ![X8]:((v1_relat_1(k2_funct_1(X8))|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(v1_funct_1(k2_funct_1(X8))|(~v1_relat_1(X8)|~v1_funct_1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.41  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v2_funct_1(esk6_0)&r2_hidden(esk5_0,k1_relat_1(esk6_0)))&(esk5_0!=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.41  fof(c_0_10, plain, ![X22]:((k2_relat_1(X22)=k1_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k1_relat_1(X22)=k2_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.41  fof(c_0_11, plain, ![X6, X7]:(~v1_relat_1(X6)|(~v1_relat_1(X7)|k1_relat_1(k5_relat_1(X6,X7))=k10_relat_1(X6,k1_relat_1(X7)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.41  cnf(c_0_12, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  cnf(c_0_13, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_15, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_16, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  fof(c_0_17, plain, ![X5]:(~v1_relat_1(X5)|k10_relat_1(X5,k2_relat_1(X5))=k1_relat_1(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.20/0.41  fof(c_0_18, plain, ![X12, X13, X14, X15, X16, X17]:(((k1_relat_1(X13)=k2_relat_1(X12)|X13!=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(((r2_hidden(X15,k1_relat_1(X12))|(~r2_hidden(X14,k2_relat_1(X12))|X15!=k1_funct_1(X13,X14))|X13!=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(X14=k1_funct_1(X12,X15)|(~r2_hidden(X14,k2_relat_1(X12))|X15!=k1_funct_1(X13,X14))|X13!=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&((r2_hidden(X16,k2_relat_1(X12))|(~r2_hidden(X17,k1_relat_1(X12))|X16!=k1_funct_1(X12,X17))|X13!=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(X17=k1_funct_1(X13,X16)|(~r2_hidden(X17,k1_relat_1(X12))|X16!=k1_funct_1(X12,X17))|X13!=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))))&(((((r2_hidden(esk4_2(X12,X13),k1_relat_1(X12))|r2_hidden(esk1_2(X12,X13),k2_relat_1(X12))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(esk3_2(X12,X13)=k1_funct_1(X12,esk4_2(X12,X13))|r2_hidden(esk1_2(X12,X13),k2_relat_1(X12))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(esk3_2(X12,X13),k2_relat_1(X12))|esk4_2(X12,X13)!=k1_funct_1(X13,esk3_2(X12,X13))|r2_hidden(esk1_2(X12,X13),k2_relat_1(X12))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(((r2_hidden(esk4_2(X12,X13),k1_relat_1(X12))|esk2_2(X12,X13)=k1_funct_1(X13,esk1_2(X12,X13))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(esk3_2(X12,X13)=k1_funct_1(X12,esk4_2(X12,X13))|esk2_2(X12,X13)=k1_funct_1(X13,esk1_2(X12,X13))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(esk3_2(X12,X13),k2_relat_1(X12))|esk4_2(X12,X13)!=k1_funct_1(X13,esk3_2(X12,X13))|esk2_2(X12,X13)=k1_funct_1(X13,esk1_2(X12,X13))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))))&(((r2_hidden(esk4_2(X12,X13),k1_relat_1(X12))|(~r2_hidden(esk2_2(X12,X13),k1_relat_1(X12))|esk1_2(X12,X13)!=k1_funct_1(X12,esk2_2(X12,X13)))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(esk3_2(X12,X13)=k1_funct_1(X12,esk4_2(X12,X13))|(~r2_hidden(esk2_2(X12,X13),k1_relat_1(X12))|esk1_2(X12,X13)!=k1_funct_1(X12,esk2_2(X12,X13)))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12))))&(~r2_hidden(esk3_2(X12,X13),k2_relat_1(X12))|esk4_2(X12,X13)!=k1_funct_1(X13,esk3_2(X12,X13))|(~r2_hidden(esk2_2(X12,X13),k1_relat_1(X12))|esk1_2(X12,X13)!=k1_funct_1(X12,esk2_2(X12,X13)))|k1_relat_1(X13)!=k2_relat_1(X12)|X13=k2_funct_1(X12)|(~v1_relat_1(X13)|~v1_funct_1(X13))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.20/0.41  cnf(c_0_19, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (k1_relat_1(k2_funct_1(esk6_0))=k2_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_13]), c_0_16]), c_0_14])])).
% 0.20/0.41  cnf(c_0_22, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_23, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(X1,k1_relat_1(X4))|X3!=k1_funct_1(X4,X1)|X2!=k2_funct_1(X4)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X4)|~v1_relat_1(X4)|~v1_funct_1(X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.41  cnf(c_0_24, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.41  fof(c_0_25, plain, ![X9, X10, X11]:(~v1_relat_1(X10)|~v1_funct_1(X10)|(~v1_relat_1(X11)|~v1_funct_1(X11)|(~r2_hidden(X9,k1_relat_1(k5_relat_1(X11,X10)))|k1_funct_1(k5_relat_1(X11,X10),X9)=k1_funct_1(X10,k1_funct_1(X11,X9))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (k1_relat_1(k5_relat_1(X1,k2_funct_1(esk6_0)))=k10_relat_1(X1,k2_relat_1(esk6_0))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (k10_relat_1(esk6_0,k2_relat_1(esk6_0))=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_14])).
% 0.20/0.41  cnf(c_0_28, plain, (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X2))=X2|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_23])]), c_0_12]), c_0_24])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_30, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (k1_relat_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)))=k1_relat_1(esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_14]), c_0_27])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_13]), c_0_14])])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (esk5_0!=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_16]), c_0_13]), c_0_14])])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),X1)=k1_funct_1(k2_funct_1(esk6_0),k1_funct_1(esk6_0,X1))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_13]), c_0_32]), c_0_14]), c_0_20])])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (k1_funct_1(k5_relat_1(esk6_0,k2_funct_1(esk6_0)),esk5_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_34]), c_0_36]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 38
% 0.20/0.41  # Proof object clause steps            : 23
% 0.20/0.41  # Proof object formula steps           : 15
% 0.20/0.41  # Proof object conjectures             : 18
% 0.20/0.41  # Proof object clause conjectures      : 15
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 12
% 0.20/0.41  # Proof object initial formulas used   : 7
% 0.20/0.41  # Proof object generating inferences   : 9
% 0.20/0.41  # Proof object simplifying inferences  : 26
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 7
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 26
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 26
% 0.20/0.41  # Processed clauses                    : 107
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 1
% 0.20/0.41  # ...remaining for further processing  : 106
% 0.20/0.41  # Other redundant clauses eliminated   : 9
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 2
% 0.20/0.41  # Generated clauses                    : 204
% 0.20/0.41  # ...of the previous two non-trivial   : 203
% 0.20/0.41  # Contextual simplify-reflections      : 8
% 0.20/0.41  # Paramodulations                      : 199
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 9
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 74
% 0.20/0.41  #    Positive orientable unit clauses  : 41
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 32
% 0.20/0.41  # Current number of unprocessed clauses: 147
% 0.20/0.41  # ...number of literals in the above   : 560
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 27
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 877
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 45
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 9
% 0.20/0.41  # Unit Clause-clause subsumption calls : 351
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 123
% 0.20/0.41  # BW rewrite match successes           : 2
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 9943
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.058 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.063 s
% 0.20/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
