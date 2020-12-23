%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0650+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:58 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 117 expanded)
%              Number of clauses        :   19 (  40 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  247 ( 807 expanded)
%              Number of equality atoms :   73 ( 234 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   3 average)
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

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_6,plain,(
    ! [X19] :
      ( ( k2_relat_1(X19) = k1_relat_1(k2_funct_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k1_relat_1(X19) = k2_relat_1(k2_funct_1(X19))
        | ~ v2_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v2_funct_1(esk6_0)
    & r2_hidden(esk5_0,k2_relat_1(esk6_0))
    & ( esk5_0 != k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))
      | esk5_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ( v1_relat_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( v1_funct_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_9,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( k1_relat_1(X10) = k2_relat_1(X9)
        | X10 != k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(X12,k1_relat_1(X9))
        | ~ r2_hidden(X11,k2_relat_1(X9))
        | X12 != k1_funct_1(X10,X11)
        | X10 != k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( X11 = k1_funct_1(X9,X12)
        | ~ r2_hidden(X11,k2_relat_1(X9))
        | X12 != k1_funct_1(X10,X11)
        | X10 != k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(X13,k2_relat_1(X9))
        | ~ r2_hidden(X14,k1_relat_1(X9))
        | X13 != k1_funct_1(X9,X14)
        | X10 != k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( X14 = k1_funct_1(X10,X13)
        | ~ r2_hidden(X14,k1_relat_1(X9))
        | X13 != k1_funct_1(X9,X14)
        | X10 != k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk4_2(X9,X10),k1_relat_1(X9))
        | r2_hidden(esk1_2(X9,X10),k2_relat_1(X9))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk3_2(X9,X10) = k1_funct_1(X9,esk4_2(X9,X10))
        | r2_hidden(esk1_2(X9,X10),k2_relat_1(X9))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(esk3_2(X9,X10),k2_relat_1(X9))
        | esk4_2(X9,X10) != k1_funct_1(X10,esk3_2(X9,X10))
        | r2_hidden(esk1_2(X9,X10),k2_relat_1(X9))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk4_2(X9,X10),k1_relat_1(X9))
        | esk2_2(X9,X10) = k1_funct_1(X10,esk1_2(X9,X10))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk3_2(X9,X10) = k1_funct_1(X9,esk4_2(X9,X10))
        | esk2_2(X9,X10) = k1_funct_1(X10,esk1_2(X9,X10))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(esk3_2(X9,X10),k2_relat_1(X9))
        | esk4_2(X9,X10) != k1_funct_1(X10,esk3_2(X9,X10))
        | esk2_2(X9,X10) = k1_funct_1(X10,esk1_2(X9,X10))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk4_2(X9,X10),k1_relat_1(X9))
        | ~ r2_hidden(esk2_2(X9,X10),k1_relat_1(X9))
        | esk1_2(X9,X10) != k1_funct_1(X9,esk2_2(X9,X10))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk3_2(X9,X10) = k1_funct_1(X9,esk4_2(X9,X10))
        | ~ r2_hidden(esk2_2(X9,X10),k1_relat_1(X9))
        | esk1_2(X9,X10) != k1_funct_1(X9,esk2_2(X9,X10))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(esk3_2(X9,X10),k2_relat_1(X9))
        | esk4_2(X9,X10) != k1_funct_1(X10,esk3_2(X9,X10))
        | ~ r2_hidden(esk2_2(X9,X10),k1_relat_1(X9))
        | esk1_2(X9,X10) != k1_funct_1(X9,esk2_2(X9,X10))
        | k1_relat_1(X10) != k2_relat_1(X9)
        | X10 = k2_funct_1(X9)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10)
        | ~ v2_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v1_relat_1(X8)
      | ~ v1_funct_1(X8)
      | ~ r2_hidden(X6,k1_relat_1(X7))
      | k1_funct_1(k5_relat_1(X7,X8),X6) = k1_funct_1(X8,k1_funct_1(X7,X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_11,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | X3 != k1_funct_1(X4,X1)
    | X4 != k2_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk6_0)) = k2_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_12]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_12]),c_0_14])])).

cnf(c_0_22,plain,
    ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X2)) = X2
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_17])]),c_0_16]),c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_0,k2_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),X1),X2) = k1_funct_1(X1,k1_funct_1(k2_funct_1(esk6_0),X2))
    | ~ r2_hidden(X2,k2_relat_1(esk6_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 != k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))
    | esk5_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_13]),c_0_12]),c_0_14])])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),X1),esk5_0) = k1_funct_1(X1,k1_funct_1(k2_funct_1(esk6_0),esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_12]),c_0_26]),c_0_14])]),c_0_28]),
    [proof]).

%------------------------------------------------------------------------------
