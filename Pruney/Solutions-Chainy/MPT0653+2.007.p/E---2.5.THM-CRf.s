%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:59 EST 2020

% Result     : Theorem 1.11s
% Output     : CNFRefutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   66 (10810 expanded)
%              Number of clauses        :   59 (3274 expanded)
%              Number of leaves         :    3 (2638 expanded)
%              Depth                    :   19
%              Number of atoms          :  435 (139464 expanded)
%              Number of equality atoms :  174 (55055 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal clause size      :  130 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t60_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k1_relat_1(X1) = k2_relat_1(X2)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & ! [X3,X4] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(X2)) )
                 => ( k1_funct_1(X1,X3) = X4
                  <=> k1_funct_1(X2,X4) = X3 ) ) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

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

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & k1_relat_1(X1) = k2_relat_1(X2)
                & k2_relat_1(X1) = k1_relat_1(X2)
                & ! [X3,X4] :
                    ( ( r2_hidden(X3,k1_relat_1(X1))
                      & r2_hidden(X4,k1_relat_1(X2)) )
                   => ( k1_funct_1(X1,X3) = X4
                    <=> k1_funct_1(X2,X4) = X3 ) ) )
             => X2 = k2_funct_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t60_funct_1])).

fof(c_0_4,negated_conjecture,(
    ! [X19,X20] :
      ( v1_relat_1(esk5_0)
      & v1_funct_1(esk5_0)
      & v1_relat_1(esk6_0)
      & v1_funct_1(esk6_0)
      & v2_funct_1(esk5_0)
      & k1_relat_1(esk5_0) = k2_relat_1(esk6_0)
      & k2_relat_1(esk5_0) = k1_relat_1(esk6_0)
      & ( k1_funct_1(esk5_0,X19) != X20
        | k1_funct_1(esk6_0,X20) = X19
        | ~ r2_hidden(X19,k1_relat_1(esk5_0))
        | ~ r2_hidden(X20,k1_relat_1(esk6_0)) )
      & ( k1_funct_1(esk6_0,X20) != X19
        | k1_funct_1(esk5_0,X19) = X20
        | ~ r2_hidden(X19,k1_relat_1(esk5_0))
        | ~ r2_hidden(X20,k1_relat_1(esk6_0)) )
      & esk6_0 != k2_funct_1(esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

cnf(c_0_5,negated_conjecture,
    ( k1_funct_1(esk5_0,X2) = X1
    | k1_funct_1(esk6_0,X1) != X2
    | ~ r2_hidden(X2,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_6,negated_conjecture,
    ( k1_relat_1(esk5_0) = k2_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | ~ r2_hidden(X5,k1_relat_1(X6))
      | r2_hidden(k1_funct_1(X6,X5),k2_relat_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( k1_relat_1(X8) = k2_relat_1(X7)
        | X8 != k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( r2_hidden(X10,k1_relat_1(X7))
        | ~ r2_hidden(X9,k2_relat_1(X7))
        | X10 != k1_funct_1(X8,X9)
        | X8 != k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X9 = k1_funct_1(X7,X10)
        | ~ r2_hidden(X9,k2_relat_1(X7))
        | X10 != k1_funct_1(X8,X9)
        | X8 != k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( r2_hidden(X11,k2_relat_1(X7))
        | ~ r2_hidden(X12,k1_relat_1(X7))
        | X11 != k1_funct_1(X7,X12)
        | X8 != k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( X12 = k1_funct_1(X8,X11)
        | ~ r2_hidden(X12,k1_relat_1(X7))
        | X11 != k1_funct_1(X7,X12)
        | X8 != k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( r2_hidden(esk4_2(X7,X8),k1_relat_1(X7))
        | r2_hidden(esk1_2(X7,X8),k2_relat_1(X7))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( esk3_2(X7,X8) = k1_funct_1(X7,esk4_2(X7,X8))
        | r2_hidden(esk1_2(X7,X8),k2_relat_1(X7))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(esk3_2(X7,X8),k2_relat_1(X7))
        | esk4_2(X7,X8) != k1_funct_1(X8,esk3_2(X7,X8))
        | r2_hidden(esk1_2(X7,X8),k2_relat_1(X7))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( r2_hidden(esk4_2(X7,X8),k1_relat_1(X7))
        | esk2_2(X7,X8) = k1_funct_1(X8,esk1_2(X7,X8))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( esk3_2(X7,X8) = k1_funct_1(X7,esk4_2(X7,X8))
        | esk2_2(X7,X8) = k1_funct_1(X8,esk1_2(X7,X8))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(esk3_2(X7,X8),k2_relat_1(X7))
        | esk4_2(X7,X8) != k1_funct_1(X8,esk3_2(X7,X8))
        | esk2_2(X7,X8) = k1_funct_1(X8,esk1_2(X7,X8))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( r2_hidden(esk4_2(X7,X8),k1_relat_1(X7))
        | ~ r2_hidden(esk2_2(X7,X8),k1_relat_1(X7))
        | esk1_2(X7,X8) != k1_funct_1(X7,esk2_2(X7,X8))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( esk3_2(X7,X8) = k1_funct_1(X7,esk4_2(X7,X8))
        | ~ r2_hidden(esk2_2(X7,X8),k1_relat_1(X7))
        | esk1_2(X7,X8) != k1_funct_1(X7,esk2_2(X7,X8))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) )
      & ( ~ r2_hidden(esk3_2(X7,X8),k2_relat_1(X7))
        | esk4_2(X7,X8) != k1_funct_1(X8,esk3_2(X7,X8))
        | ~ r2_hidden(esk2_2(X7,X8),k1_relat_1(X7))
        | esk1_2(X7,X8) != k1_funct_1(X7,esk2_2(X7,X8))
        | k1_relat_1(X8) != k2_relat_1(X7)
        | X8 = k2_funct_1(X7)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8)
        | ~ v2_funct_1(X7)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

cnf(c_0_10,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) = X2
    | k1_funct_1(esk6_0,X2) != X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0))
    | ~ r2_hidden(X2,k2_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_5,c_0_6]),c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_13,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_14,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1)) = X2
    | k1_funct_1(esk6_0,X2) != k1_funct_1(esk6_0,X1)
    | ~ r2_hidden(X2,k2_relat_1(esk5_0))
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_7]),c_0_12]),c_0_13])])).

cnf(c_0_19,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,X1)) = esk3_2(esk5_0,X1)
    | k1_funct_1(X1,esk1_2(esk5_0,X1)) = esk2_2(esk5_0,X1)
    | X1 = k2_funct_1(esk5_0)
    | k1_relat_1(X1) != k2_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,X1)) = esk3_2(esk5_0,X1)
    | k1_funct_1(esk5_0,k1_funct_1(esk6_0,X2)) = esk1_2(esk5_0,X1)
    | X1 = k2_funct_1(esk5_0)
    | k1_funct_1(esk6_0,esk1_2(esk5_0,X1)) != k1_funct_1(esk6_0,X2)
    | k1_relat_1(X1) != k2_relat_1(esk5_0)
    | ~ r2_hidden(X2,k2_relat_1(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( esk6_0 != k2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk6_0,X2) = X1
    | k1_funct_1(esk5_0,X1) != X2
    | ~ r2_hidden(X1,k1_relat_1(esk5_0))
    | ~ r2_hidden(X2,k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,X1)) = esk3_2(esk5_0,X1)
    | X1 = k2_funct_1(esk5_0)
    | r2_hidden(esk2_2(esk5_0,X1),k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(esk5_0)
    | ~ r2_hidden(esk1_2(esk5_0,X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0)) = esk3_2(esk5_0,esk6_0)
    | k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1)) = esk1_2(esk5_0,esk6_0)
    | esk2_2(esk5_0,esk6_0) != k1_funct_1(esk6_0,X1)
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_7]),c_0_12]),c_0_13])]),c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = X2
    | k1_funct_1(esk5_0,X2) != X1
    | ~ r2_hidden(X1,k2_relat_1(esk5_0))
    | ~ r2_hidden(X2,k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_7]),c_0_6])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(X1,esk1_2(esk5_0,X1)) = esk2_2(esk5_0,X1)
    | X1 = k2_funct_1(esk5_0)
    | r2_hidden(esk4_2(esk5_0,X1),k2_relat_1(esk6_0))
    | k1_relat_1(X1) != k2_relat_1(esk5_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_15]),c_0_6]),c_0_16]),c_0_17])])).

cnf(c_0_29,plain,
    ( esk3_2(X1,X2) = k1_funct_1(X1,esk4_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0)) = esk3_2(esk5_0,esk6_0)
    | r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_7]),c_0_12]),c_0_13])]),c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0)
    | k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0)) = esk3_2(esk5_0,esk6_0)
    | ~ r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_7]),c_0_12]),c_0_13])]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(esk5_0,X1)) = X2
    | k1_funct_1(esk5_0,X2) != k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X2,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_11]),c_0_6]),c_0_16]),c_0_17])])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0)) = esk2_2(esk5_0,esk6_0)
    | r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_7]),c_0_12]),c_0_13])]),c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,X1)) = esk3_2(esk5_0,X1)
    | X1 = k2_funct_1(esk5_0)
    | k1_funct_1(esk5_0,esk2_2(esk5_0,X1)) != esk1_2(esk5_0,X1)
    | k1_relat_1(X1) != k2_relat_1(esk5_0)
    | ~ r2_hidden(esk2_2(esk5_0,X1),k2_relat_1(esk6_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_6]),c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0)) = esk3_2(esk5_0,esk6_0)
    | r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_7]),c_0_15]),c_0_12]),c_0_16]),c_0_13]),c_0_17])]),c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0)) = esk3_2(esk5_0,esk6_0)
    | k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0)) = esk1_2(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_19]),c_0_7]),c_0_15]),c_0_12]),c_0_16]),c_0_13]),c_0_17])]),c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0)) = esk2_2(esk5_0,esk6_0)
    | k1_funct_1(esk6_0,k1_funct_1(esk5_0,X1)) = esk4_2(esk5_0,esk6_0)
    | k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0)) != k1_funct_1(esk5_0,X1)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0)) = esk3_2(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_7]),c_0_12]),c_0_13])]),c_0_22]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0))) = esk4_2(esk5_0,esk6_0)
    | k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0)) = esk2_2(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_33])).

cnf(c_0_40,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X2,esk1_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_2(esk5_0,esk6_0),k2_relat_1(esk5_0))
    | ~ r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_38]),c_0_6]),c_0_16]),c_0_17])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0)) = esk2_2(esk5_0,esk6_0)
    | k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) = esk4_2(esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0)) = esk2_2(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_7]),c_0_15]),c_0_12]),c_0_16]),c_0_13]),c_0_17])]),c_0_22]),c_0_33]),c_0_42])).

cnf(c_0_44,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_43]),c_0_7]),c_0_12]),c_0_13])])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1)) = esk1_2(esk5_0,X2)
    | X2 = k2_funct_1(esk5_0)
    | r2_hidden(esk4_2(esk5_0,X2),k2_relat_1(esk6_0))
    | k1_funct_1(esk6_0,esk1_2(esk5_0,X2)) != k1_funct_1(esk6_0,X1)
    | k1_relat_1(X2) != k2_relat_1(esk5_0)
    | ~ r2_hidden(X1,k2_relat_1(esk5_0))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_44]),c_0_6]),c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_49,negated_conjecture,
    ( X1 = k2_funct_1(esk5_0)
    | r2_hidden(esk4_2(esk5_0,X1),k2_relat_1(esk6_0))
    | k1_funct_1(esk5_0,esk2_2(esk5_0,X1)) != esk1_2(esk5_0,X1)
    | k1_relat_1(X1) != k2_relat_1(esk5_0)
    | ~ r2_hidden(esk2_2(esk5_0,X1),k2_relat_1(esk6_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_6]),c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))
    | r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_6]),c_0_7]),c_0_15]),c_0_12]),c_0_16]),c_0_13]),c_0_17])]),c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0))
    | k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) != esk4_2(esk5_0,esk6_0)
    | ~ r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_7]),c_0_15]),c_0_12]),c_0_16]),c_0_13]),c_0_17])]),c_0_22])).

cnf(c_0_52,plain,
    ( X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X2,esk3_2(X1,X2))
    | ~ r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | esk1_2(X1,X2) != k1_funct_1(X1,esk2_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(esk6_0,esk1_2(esk5_0,X1))) = esk1_2(esk5_0,X1)
    | X1 = k2_funct_1(esk5_0)
    | r2_hidden(esk4_2(esk5_0,X1),k2_relat_1(esk6_0))
    | k1_relat_1(X1) != k2_relat_1(esk5_0)
    | ~ r2_hidden(esk1_2(esk5_0,X1),k2_relat_1(esk5_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))
    | k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0)) != esk1_2(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_7]),c_0_12]),c_0_13])]),c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))
    | k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) != esk4_2(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_51]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0)) != esk1_2(esk5_0,esk6_0)
    | k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) != esk4_2(esk5_0,esk6_0)
    | ~ r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_7]),c_0_15]),c_0_6]),c_0_12]),c_0_16]),c_0_13]),c_0_17])]),c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_43]),c_0_7]),c_0_12]),c_0_13])]),c_0_22]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0)) = X1
    | k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) != esk4_2(esk5_0,esk6_0)
    | k1_funct_1(esk6_0,X1) != esk2_2(esk5_0,esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0)) != esk1_2(esk5_0,esk6_0)
    | k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) != esk4_2(esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_55]),c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) = X1
    | k1_funct_1(esk5_0,X1) != esk3_2(esk5_0,esk6_0)
    | ~ r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_41])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_44]),c_0_6]),c_0_7]),c_0_15]),c_0_12]),c_0_16]),c_0_13]),c_0_17])]),c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) != esk4_2(esk5_0,esk6_0)
    | ~ r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_43])]),c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) = X1
    | k1_funct_1(esk5_0,X1) != esk3_2(esk5_0,esk6_0)
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_64,negated_conjecture,
    ( k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0)) != esk4_2(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_61])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_38])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.11/1.33  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_AE_CS_SP_PI_S0Y
% 1.11/1.33  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.11/1.33  #
% 1.11/1.33  # Preprocessing time       : 0.027 s
% 1.11/1.33  
% 1.11/1.33  # Proof found!
% 1.11/1.33  # SZS status Theorem
% 1.11/1.33  # SZS output start CNFRefutation
% 1.11/1.33  fof(t60_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((((v2_funct_1(X1)&k1_relat_1(X1)=k2_relat_1(X2))&k2_relat_1(X1)=k1_relat_1(X2))&![X3, X4]:((r2_hidden(X3,k1_relat_1(X1))&r2_hidden(X4,k1_relat_1(X2)))=>(k1_funct_1(X1,X3)=X4<=>k1_funct_1(X2,X4)=X3)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_1)).
% 1.11/1.33  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.11/1.33  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 1.11/1.33  fof(c_0_3, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((((v2_funct_1(X1)&k1_relat_1(X1)=k2_relat_1(X2))&k2_relat_1(X1)=k1_relat_1(X2))&![X3, X4]:((r2_hidden(X3,k1_relat_1(X1))&r2_hidden(X4,k1_relat_1(X2)))=>(k1_funct_1(X1,X3)=X4<=>k1_funct_1(X2,X4)=X3)))=>X2=k2_funct_1(X1))))), inference(assume_negation,[status(cth)],[t60_funct_1])).
% 1.11/1.33  fof(c_0_4, negated_conjecture, ![X19, X20]:((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((((v2_funct_1(esk5_0)&k1_relat_1(esk5_0)=k2_relat_1(esk6_0))&k2_relat_1(esk5_0)=k1_relat_1(esk6_0))&((k1_funct_1(esk5_0,X19)!=X20|k1_funct_1(esk6_0,X20)=X19|(~r2_hidden(X19,k1_relat_1(esk5_0))|~r2_hidden(X20,k1_relat_1(esk6_0))))&(k1_funct_1(esk6_0,X20)!=X19|k1_funct_1(esk5_0,X19)=X20|(~r2_hidden(X19,k1_relat_1(esk5_0))|~r2_hidden(X20,k1_relat_1(esk6_0))))))&esk6_0!=k2_funct_1(esk5_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).
% 1.11/1.33  cnf(c_0_5, negated_conjecture, (k1_funct_1(esk5_0,X2)=X1|k1_funct_1(esk6_0,X1)!=X2|~r2_hidden(X2,k1_relat_1(esk5_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_6, negated_conjecture, (k1_relat_1(esk5_0)=k2_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_7, negated_conjecture, (k2_relat_1(esk5_0)=k1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  fof(c_0_8, plain, ![X5, X6]:(~v1_relat_1(X6)|~v1_funct_1(X6)|(~r2_hidden(X5,k1_relat_1(X6))|r2_hidden(k1_funct_1(X6,X5),k2_relat_1(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 1.11/1.33  fof(c_0_9, plain, ![X7, X8, X9, X10, X11, X12]:(((k1_relat_1(X8)=k2_relat_1(X7)|X8!=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(((r2_hidden(X10,k1_relat_1(X7))|(~r2_hidden(X9,k2_relat_1(X7))|X10!=k1_funct_1(X8,X9))|X8!=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(X9=k1_funct_1(X7,X10)|(~r2_hidden(X9,k2_relat_1(X7))|X10!=k1_funct_1(X8,X9))|X8!=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7))))&((r2_hidden(X11,k2_relat_1(X7))|(~r2_hidden(X12,k1_relat_1(X7))|X11!=k1_funct_1(X7,X12))|X8!=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(X12=k1_funct_1(X8,X11)|(~r2_hidden(X12,k1_relat_1(X7))|X11!=k1_funct_1(X7,X12))|X8!=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7))))))&(((((r2_hidden(esk4_2(X7,X8),k1_relat_1(X7))|r2_hidden(esk1_2(X7,X8),k2_relat_1(X7))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(esk3_2(X7,X8)=k1_funct_1(X7,esk4_2(X7,X8))|r2_hidden(esk1_2(X7,X8),k2_relat_1(X7))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7))))&(~r2_hidden(esk3_2(X7,X8),k2_relat_1(X7))|esk4_2(X7,X8)!=k1_funct_1(X8,esk3_2(X7,X8))|r2_hidden(esk1_2(X7,X8),k2_relat_1(X7))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7))))&(((r2_hidden(esk4_2(X7,X8),k1_relat_1(X7))|esk2_2(X7,X8)=k1_funct_1(X8,esk1_2(X7,X8))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(esk3_2(X7,X8)=k1_funct_1(X7,esk4_2(X7,X8))|esk2_2(X7,X8)=k1_funct_1(X8,esk1_2(X7,X8))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7))))&(~r2_hidden(esk3_2(X7,X8),k2_relat_1(X7))|esk4_2(X7,X8)!=k1_funct_1(X8,esk3_2(X7,X8))|esk2_2(X7,X8)=k1_funct_1(X8,esk1_2(X7,X8))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))))&(((r2_hidden(esk4_2(X7,X8),k1_relat_1(X7))|(~r2_hidden(esk2_2(X7,X8),k1_relat_1(X7))|esk1_2(X7,X8)!=k1_funct_1(X7,esk2_2(X7,X8)))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))&(esk3_2(X7,X8)=k1_funct_1(X7,esk4_2(X7,X8))|(~r2_hidden(esk2_2(X7,X8),k1_relat_1(X7))|esk1_2(X7,X8)!=k1_funct_1(X7,esk2_2(X7,X8)))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7))))&(~r2_hidden(esk3_2(X7,X8),k2_relat_1(X7))|esk4_2(X7,X8)!=k1_funct_1(X8,esk3_2(X7,X8))|(~r2_hidden(esk2_2(X7,X8),k1_relat_1(X7))|esk1_2(X7,X8)!=k1_funct_1(X7,esk2_2(X7,X8)))|k1_relat_1(X8)!=k2_relat_1(X7)|X8=k2_funct_1(X7)|(~v1_relat_1(X8)|~v1_funct_1(X8))|~v2_funct_1(X7)|(~v1_relat_1(X7)|~v1_funct_1(X7)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 1.11/1.33  cnf(c_0_10, negated_conjecture, (k1_funct_1(esk5_0,X1)=X2|k1_funct_1(esk6_0,X2)!=X1|~r2_hidden(X1,k2_relat_1(esk6_0))|~r2_hidden(X2,k2_relat_1(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_5, c_0_6]), c_0_7])).
% 1.11/1.33  cnf(c_0_11, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.11/1.33  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_13, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_14, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk4_2(X1,X2))|esk2_2(X1,X2)=k1_funct_1(X2,esk1_2(X1,X2))|X2=k2_funct_1(X1)|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_15, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_18, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1))=X2|k1_funct_1(esk6_0,X2)!=k1_funct_1(esk6_0,X1)|~r2_hidden(X2,k2_relat_1(esk5_0))|~r2_hidden(X1,k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_7]), c_0_12]), c_0_13])])).
% 1.11/1.33  cnf(c_0_19, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk4_2(X1,X2))|r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))|X2=k2_funct_1(X1)|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_20, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,X1))=esk3_2(esk5_0,X1)|k1_funct_1(X1,esk1_2(esk5_0,X1))=esk2_2(esk5_0,X1)|X1=k2_funct_1(esk5_0)|k1_relat_1(X1)!=k2_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])).
% 1.11/1.33  cnf(c_0_21, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,X1))=esk3_2(esk5_0,X1)|k1_funct_1(esk5_0,k1_funct_1(esk6_0,X2))=esk1_2(esk5_0,X1)|X1=k2_funct_1(esk5_0)|k1_funct_1(esk6_0,esk1_2(esk5_0,X1))!=k1_funct_1(esk6_0,X2)|k1_relat_1(X1)!=k2_relat_1(esk5_0)|~r2_hidden(X2,k2_relat_1(esk5_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_15]), c_0_16]), c_0_17])])).
% 1.11/1.33  cnf(c_0_22, negated_conjecture, (esk6_0!=k2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_23, negated_conjecture, (k1_funct_1(esk6_0,X2)=X1|k1_funct_1(esk5_0,X1)!=X2|~r2_hidden(X1,k1_relat_1(esk5_0))|~r2_hidden(X2,k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_4])).
% 1.11/1.33  cnf(c_0_24, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|esk2_2(X1,X2)=k1_funct_1(X2,esk1_2(X1,X2))|X2=k2_funct_1(X1)|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_25, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,X1))=esk3_2(esk5_0,X1)|X1=k2_funct_1(esk5_0)|r2_hidden(esk2_2(esk5_0,X1),k2_relat_1(X1))|k1_relat_1(X1)!=k2_relat_1(esk5_0)|~r2_hidden(esk1_2(esk5_0,X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_20])).
% 1.11/1.33  cnf(c_0_26, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0))=esk3_2(esk5_0,esk6_0)|k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1))=esk1_2(esk5_0,esk6_0)|esk2_2(esk5_0,esk6_0)!=k1_funct_1(esk6_0,X1)|~r2_hidden(X1,k2_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_7]), c_0_12]), c_0_13])]), c_0_22])).
% 1.11/1.33  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk6_0,X1)=X2|k1_funct_1(esk5_0,X2)!=X1|~r2_hidden(X1,k2_relat_1(esk5_0))|~r2_hidden(X2,k2_relat_1(esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_7]), c_0_6])).
% 1.11/1.33  cnf(c_0_28, negated_conjecture, (k1_funct_1(X1,esk1_2(esk5_0,X1))=esk2_2(esk5_0,X1)|X1=k2_funct_1(esk5_0)|r2_hidden(esk4_2(esk5_0,X1),k2_relat_1(esk6_0))|k1_relat_1(X1)!=k2_relat_1(esk5_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_15]), c_0_6]), c_0_16]), c_0_17])])).
% 1.11/1.33  cnf(c_0_29, plain, (esk3_2(X1,X2)=k1_funct_1(X1,esk4_2(X1,X2))|X2=k2_funct_1(X1)|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|esk1_2(X1,X2)!=k1_funct_1(X1,esk2_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_30, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0))=esk3_2(esk5_0,esk6_0)|r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))|~r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_7]), c_0_12]), c_0_13])]), c_0_22])).
% 1.11/1.33  cnf(c_0_31, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0))=esk1_2(esk5_0,esk6_0)|k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0))=esk3_2(esk5_0,esk6_0)|~r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_20]), c_0_7]), c_0_12]), c_0_13])]), c_0_22])).
% 1.11/1.33  cnf(c_0_32, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(esk5_0,X1))=X2|k1_funct_1(esk5_0,X2)!=k1_funct_1(esk5_0,X1)|~r2_hidden(X2,k2_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_11]), c_0_6]), c_0_16]), c_0_17])])).
% 1.11/1.33  cnf(c_0_33, negated_conjecture, (k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0))=esk2_2(esk5_0,esk6_0)|r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_7]), c_0_12]), c_0_13])]), c_0_22])).
% 1.11/1.33  cnf(c_0_34, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,X1))=esk3_2(esk5_0,X1)|X1=k2_funct_1(esk5_0)|k1_funct_1(esk5_0,esk2_2(esk5_0,X1))!=esk1_2(esk5_0,X1)|k1_relat_1(X1)!=k2_relat_1(esk5_0)|~r2_hidden(esk2_2(esk5_0,X1),k2_relat_1(esk6_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_6]), c_0_15]), c_0_16]), c_0_17])])).
% 1.11/1.33  cnf(c_0_35, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0))=esk3_2(esk5_0,esk6_0)|r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_19]), c_0_7]), c_0_15]), c_0_12]), c_0_16]), c_0_13]), c_0_17])]), c_0_22])).
% 1.11/1.33  cnf(c_0_36, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0))=esk3_2(esk5_0,esk6_0)|k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0))=esk1_2(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_19]), c_0_7]), c_0_15]), c_0_12]), c_0_16]), c_0_13]), c_0_17])]), c_0_22])).
% 1.11/1.33  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0))=esk2_2(esk5_0,esk6_0)|k1_funct_1(esk6_0,k1_funct_1(esk5_0,X1))=esk4_2(esk5_0,esk6_0)|k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0))!=k1_funct_1(esk5_0,X1)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 1.11/1.33  cnf(c_0_38, negated_conjecture, (k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0))=esk3_2(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_7]), c_0_12]), c_0_13])]), c_0_22]), c_0_36])).
% 1.11/1.33  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(esk5_0,esk4_2(esk5_0,esk6_0)))=esk4_2(esk5_0,esk6_0)|k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0))=esk2_2(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_37]), c_0_33])).
% 1.11/1.33  cnf(c_0_40, plain, (esk2_2(X1,X2)=k1_funct_1(X2,esk1_2(X1,X2))|X2=k2_funct_1(X1)|~r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))|esk4_2(X1,X2)!=k1_funct_1(X2,esk3_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_2(esk5_0,esk6_0),k2_relat_1(esk5_0))|~r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_38]), c_0_6]), c_0_16]), c_0_17])])).
% 1.11/1.33  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0))=esk2_2(esk5_0,esk6_0)|k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))=esk4_2(esk5_0,esk6_0)), inference(rw,[status(thm)],[c_0_39, c_0_38])).
% 1.11/1.33  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk6_0,esk1_2(esk5_0,esk6_0))=esk2_2(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_7]), c_0_15]), c_0_12]), c_0_16]), c_0_13]), c_0_17])]), c_0_22]), c_0_33]), c_0_42])).
% 1.11/1.33  cnf(c_0_44, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))|X2=k2_funct_1(X1)|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_45, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|X2=k2_funct_1(X1)|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|esk1_2(X1,X2)!=k1_funct_1(X1,esk2_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_46, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))|~r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_43]), c_0_7]), c_0_12]), c_0_13])])).
% 1.11/1.33  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),k2_relat_1(X1))|X2=k2_funct_1(X1)|~r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))|esk4_2(X1,X2)!=k1_funct_1(X2,esk3_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_48, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(esk6_0,X1))=esk1_2(esk5_0,X2)|X2=k2_funct_1(esk5_0)|r2_hidden(esk4_2(esk5_0,X2),k2_relat_1(esk6_0))|k1_funct_1(esk6_0,esk1_2(esk5_0,X2))!=k1_funct_1(esk6_0,X1)|k1_relat_1(X2)!=k2_relat_1(esk5_0)|~r2_hidden(X1,k2_relat_1(esk5_0))|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_44]), c_0_6]), c_0_15]), c_0_16]), c_0_17])])).
% 1.11/1.33  cnf(c_0_49, negated_conjecture, (X1=k2_funct_1(esk5_0)|r2_hidden(esk4_2(esk5_0,X1),k2_relat_1(esk6_0))|k1_funct_1(esk5_0,esk2_2(esk5_0,X1))!=esk1_2(esk5_0,X1)|k1_relat_1(X1)!=k2_relat_1(esk5_0)|~r2_hidden(esk2_2(esk5_0,X1),k2_relat_1(esk6_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_6]), c_0_15]), c_0_16]), c_0_17])])).
% 1.11/1.33  cnf(c_0_50, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))|r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_44]), c_0_6]), c_0_7]), c_0_15]), c_0_12]), c_0_16]), c_0_13]), c_0_17])]), c_0_22])).
% 1.11/1.33  cnf(c_0_51, negated_conjecture, (r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0))|k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))!=esk4_2(esk5_0,esk6_0)|~r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_7]), c_0_15]), c_0_12]), c_0_16]), c_0_13]), c_0_17])]), c_0_22])).
% 1.11/1.33  cnf(c_0_52, plain, (X2=k2_funct_1(X1)|~r2_hidden(esk3_2(X1,X2),k2_relat_1(X1))|esk4_2(X1,X2)!=k1_funct_1(X2,esk3_2(X1,X2))|~r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|esk1_2(X1,X2)!=k1_funct_1(X1,esk2_2(X1,X2))|k1_relat_1(X2)!=k2_relat_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.11/1.33  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(esk6_0,esk1_2(esk5_0,X1)))=esk1_2(esk5_0,X1)|X1=k2_funct_1(esk5_0)|r2_hidden(esk4_2(esk5_0,X1),k2_relat_1(esk6_0))|k1_relat_1(X1)!=k2_relat_1(esk5_0)|~r2_hidden(esk1_2(esk5_0,X1),k2_relat_1(esk5_0))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_48])).
% 1.11/1.33  cnf(c_0_54, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))|k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0))!=esk1_2(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_7]), c_0_12]), c_0_13])]), c_0_22])).
% 1.11/1.33  cnf(c_0_55, negated_conjecture, (r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))|k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))!=esk4_2(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_51]), c_0_50])).
% 1.11/1.33  cnf(c_0_56, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0))!=esk1_2(esk5_0,esk6_0)|k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))!=esk4_2(esk5_0,esk6_0)|~r2_hidden(esk2_2(esk5_0,esk6_0),k2_relat_1(esk6_0))|~r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_7]), c_0_15]), c_0_6]), c_0_12]), c_0_16]), c_0_13]), c_0_17])]), c_0_22])).
% 1.11/1.33  cnf(c_0_57, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))|~r2_hidden(esk1_2(esk5_0,esk6_0),k2_relat_1(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_43]), c_0_7]), c_0_12]), c_0_13])]), c_0_22]), c_0_54])).
% 1.11/1.33  cnf(c_0_58, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0))=X1|k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))!=esk4_2(esk5_0,esk6_0)|k1_funct_1(esk6_0,X1)!=esk2_2(esk5_0,esk6_0)|~r2_hidden(X1,k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_10, c_0_55])).
% 1.11/1.33  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk5_0,esk2_2(esk5_0,esk6_0))!=esk1_2(esk5_0,esk6_0)|k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))!=esk4_2(esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_55]), c_0_54])).
% 1.11/1.33  cnf(c_0_60, negated_conjecture, (k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))=X1|k1_funct_1(esk5_0,X1)!=esk3_2(esk5_0,esk6_0)|~r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_41])).
% 1.11/1.33  cnf(c_0_61, negated_conjecture, (r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_44]), c_0_6]), c_0_7]), c_0_15]), c_0_12]), c_0_16]), c_0_13]), c_0_17])]), c_0_22])).
% 1.11/1.33  cnf(c_0_62, negated_conjecture, (k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))!=esk4_2(esk5_0,esk6_0)|~r2_hidden(esk4_2(esk5_0,esk6_0),k2_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_51]), c_0_43])]), c_0_59])).
% 1.11/1.33  cnf(c_0_63, negated_conjecture, (k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))=X1|k1_funct_1(esk5_0,X1)!=esk3_2(esk5_0,esk6_0)|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 1.11/1.33  cnf(c_0_64, negated_conjecture, (k1_funct_1(esk6_0,esk3_2(esk5_0,esk6_0))!=esk4_2(esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_61])])).
% 1.11/1.33  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_61]), c_0_38])]), c_0_64]), ['proof']).
% 1.11/1.33  # SZS output end CNFRefutation
% 1.11/1.33  # Proof object total steps             : 66
% 1.11/1.33  # Proof object clause steps            : 59
% 1.11/1.33  # Proof object formula steps           : 7
% 1.11/1.33  # Proof object conjectures             : 52
% 1.11/1.33  # Proof object clause conjectures      : 49
% 1.11/1.33  # Proof object formula conjectures     : 3
% 1.11/1.33  # Proof object initial clauses used    : 20
% 1.11/1.33  # Proof object initial formulas used   : 3
% 1.11/1.33  # Proof object generating inferences   : 34
% 1.11/1.33  # Proof object simplifying inferences  : 154
% 1.11/1.33  # Training examples: 0 positive, 0 negative
% 1.11/1.33  # Parsed axioms                        : 3
% 1.11/1.33  # Removed by relevancy pruning/SinE    : 0
% 1.11/1.33  # Initial clauses                      : 25
% 1.11/1.33  # Removed in clause preprocessing      : 0
% 1.11/1.33  # Initial clauses in saturation        : 25
% 1.11/1.33  # Processed clauses                    : 5453
% 1.11/1.33  # ...of these trivial                  : 518
% 1.11/1.33  # ...subsumed                          : 3617
% 1.11/1.33  # ...remaining for further processing  : 1318
% 1.11/1.33  # Other redundant clauses eliminated   : 0
% 1.11/1.33  # Clauses deleted for lack of memory   : 0
% 1.11/1.33  # Backward-subsumed                    : 457
% 1.11/1.33  # Backward-rewritten                   : 330
% 1.11/1.33  # Generated clauses                    : 48046
% 1.11/1.33  # ...of the previous two non-trivial   : 45310
% 1.11/1.33  # Contextual simplify-reflections      : 129
% 1.11/1.33  # Paramodulations                      : 47723
% 1.11/1.33  # Factorizations                       : 3
% 1.11/1.33  # Equation resolutions                 : 320
% 1.11/1.33  # Propositional unsat checks           : 0
% 1.11/1.33  #    Propositional check models        : 0
% 1.11/1.33  #    Propositional check unsatisfiable : 0
% 1.11/1.33  #    Propositional clauses             : 0
% 1.11/1.33  #    Propositional clauses after purity: 0
% 1.11/1.33  #    Propositional unsat core size     : 0
% 1.11/1.33  #    Propositional preprocessing time  : 0.000
% 1.11/1.33  #    Propositional encoding time       : 0.000
% 1.11/1.33  #    Propositional solver time         : 0.000
% 1.11/1.33  #    Success case prop preproc time    : 0.000
% 1.11/1.33  #    Success case prop encoding time   : 0.000
% 1.11/1.33  #    Success case prop solver time     : 0.000
% 1.11/1.33  # Current number of processed clauses  : 531
% 1.11/1.33  #    Positive orientable unit clauses  : 12
% 1.11/1.33  #    Positive unorientable unit clauses: 0
% 1.11/1.33  #    Negative unit clauses             : 2
% 1.11/1.33  #    Non-unit-clauses                  : 517
% 1.11/1.33  # Current number of unprocessed clauses: 39328
% 1.11/1.33  # ...number of literals in the above   : 391975
% 1.11/1.33  # Current number of archived formulas  : 0
% 1.11/1.33  # Current number of archived clauses   : 787
% 1.11/1.33  # Clause-clause subsumption calls (NU) : 149758
% 1.11/1.33  # Rec. Clause-clause subsumption calls : 7614
% 1.11/1.33  # Non-unit clause-clause subsumptions  : 3371
% 1.11/1.33  # Unit Clause-clause subsumption calls : 1964
% 1.11/1.33  # Rewrite failures with RHS unbound    : 0
% 1.11/1.33  # BW rewrite match attempts            : 3
% 1.11/1.33  # BW rewrite match successes           : 3
% 1.11/1.33  # Condensation attempts                : 0
% 1.11/1.33  # Condensation successes               : 0
% 1.11/1.33  # Termbank termtop insertions          : 1724977
% 1.11/1.33  
% 1.11/1.33  # -------------------------------------------------
% 1.11/1.33  # User time                : 0.969 s
% 1.11/1.33  # System time              : 0.023 s
% 1.11/1.33  # Total time               : 0.992 s
% 1.11/1.33  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
