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
% DateTime   : Thu Dec  3 10:53:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 258 expanded)
%              Number of clauses        :   36 (  88 expanded)
%              Number of leaves         :    6 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 (2465 expanded)
%              Number of equality atoms :  114 ( 932 expanded)
%              Maximal formula depth    :   31 (   6 average)
%              Maximal clause size      :  130 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(t57_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( k1_relat_1(X7) = k2_relat_1(X6)
        | X7 != k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(X9,k1_relat_1(X6))
        | ~ r2_hidden(X8,k2_relat_1(X6))
        | X9 != k1_funct_1(X7,X8)
        | X7 != k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X8 = k1_funct_1(X6,X9)
        | ~ r2_hidden(X8,k2_relat_1(X6))
        | X9 != k1_funct_1(X7,X8)
        | X7 != k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(X10,k2_relat_1(X6))
        | ~ r2_hidden(X11,k1_relat_1(X6))
        | X10 != k1_funct_1(X6,X11)
        | X7 != k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( X11 = k1_funct_1(X7,X10)
        | ~ r2_hidden(X11,k1_relat_1(X6))
        | X10 != k1_funct_1(X6,X11)
        | X7 != k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk4_2(X6,X7),k1_relat_1(X6))
        | r2_hidden(esk1_2(X6,X7),k2_relat_1(X6))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk3_2(X6,X7) = k1_funct_1(X6,esk4_2(X6,X7))
        | r2_hidden(esk1_2(X6,X7),k2_relat_1(X6))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk3_2(X6,X7),k2_relat_1(X6))
        | esk4_2(X6,X7) != k1_funct_1(X7,esk3_2(X6,X7))
        | r2_hidden(esk1_2(X6,X7),k2_relat_1(X6))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk4_2(X6,X7),k1_relat_1(X6))
        | esk2_2(X6,X7) = k1_funct_1(X7,esk1_2(X6,X7))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk3_2(X6,X7) = k1_funct_1(X6,esk4_2(X6,X7))
        | esk2_2(X6,X7) = k1_funct_1(X7,esk1_2(X6,X7))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk3_2(X6,X7),k2_relat_1(X6))
        | esk4_2(X6,X7) != k1_funct_1(X7,esk3_2(X6,X7))
        | esk2_2(X6,X7) = k1_funct_1(X7,esk1_2(X6,X7))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( r2_hidden(esk4_2(X6,X7),k1_relat_1(X6))
        | ~ r2_hidden(esk2_2(X6,X7),k1_relat_1(X6))
        | esk1_2(X6,X7) != k1_funct_1(X6,esk2_2(X6,X7))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( esk3_2(X6,X7) = k1_funct_1(X6,esk4_2(X6,X7))
        | ~ r2_hidden(esk2_2(X6,X7),k1_relat_1(X6))
        | esk1_2(X6,X7) != k1_funct_1(X6,esk2_2(X6,X7))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( ~ r2_hidden(esk3_2(X6,X7),k2_relat_1(X6))
        | esk4_2(X6,X7) != k1_funct_1(X7,esk3_2(X6,X7))
        | ~ r2_hidden(esk2_2(X6,X7),k1_relat_1(X6))
        | esk1_2(X6,X7) != k1_funct_1(X6,esk2_2(X6,X7))
        | k1_relat_1(X7) != k2_relat_1(X6)
        | X7 = k2_funct_1(X6)
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ( v1_relat_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( v1_funct_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_9,negated_conjecture,(
    ! [X24,X25] :
      ( v1_relat_1(esk6_0)
      & v1_funct_1(esk6_0)
      & v1_relat_1(esk7_0)
      & v1_funct_1(esk7_0)
      & v2_funct_1(esk6_0)
      & k1_relat_1(esk6_0) = k2_relat_1(esk7_0)
      & k2_relat_1(esk6_0) = k1_relat_1(esk7_0)
      & ( k1_funct_1(esk6_0,X24) != X25
        | k1_funct_1(esk7_0,X25) = X24
        | ~ r2_hidden(X24,k1_relat_1(esk6_0))
        | ~ r2_hidden(X25,k1_relat_1(esk7_0)) )
      & ( k1_funct_1(esk7_0,X25) != X24
        | k1_funct_1(esk6_0,X24) = X25
        | ~ r2_hidden(X24,k1_relat_1(esk6_0))
        | ~ r2_hidden(X25,k1_relat_1(esk7_0)) )
      & esk7_0 != k2_funct_1(esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_funct_1(X2,X3)
    | X4 != k2_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
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

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( ( r2_hidden(esk5_2(X19,X20),k1_relat_1(X19))
        | k1_relat_1(X19) != k1_relat_1(X20)
        | X19 = X20
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( k1_funct_1(X19,esk5_2(X19,X20)) != k1_funct_1(X20,esk5_2(X19,X20))
        | k1_relat_1(X19) != k1_relat_1(X20)
        | X19 = X20
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

fof(c_0_14,plain,(
    ! [X16] :
      ( ( k2_relat_1(X16) = k1_relat_1(k2_funct_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k1_relat_1(X16) = k2_relat_1(k2_funct_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_15,negated_conjecture,
    ( k1_funct_1(esk7_0,X2) = X1
    | k1_funct_1(esk6_0,X1) != X2
    | ~ r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X2,k1_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])]),c_0_11]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X3,k2_relat_1(X2))
    | X1 != k1_funct_1(X4,X3)
    | X4 != k2_funct_1(X2)
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_22,plain,(
    ! [X17,X18] :
      ( ( X17 = k1_funct_1(X18,k1_funct_1(k2_funct_1(X18),X17))
        | ~ v2_funct_1(X18)
        | ~ r2_hidden(X17,k2_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X17 = k1_funct_1(k5_relat_1(k2_funct_1(X18),X18),X17)
        | ~ v2_funct_1(X18)
        | ~ r2_hidden(X17,k2_relat_1(X18))
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_funct_1])])])).

cnf(c_0_23,plain,
    ( r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1)) = X1
    | ~ r2_hidden(k1_funct_1(esk6_0,X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,X1),k1_relat_1(esk7_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_29,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])]),c_0_11]),c_0_12])).

cnf(c_0_30,plain,
    ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( X1 = esk7_0
    | r2_hidden(esk5_2(X1,esk7_0),k1_relat_1(X1))
    | k1_relat_1(X1) != k1_relat_1(esk7_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk6_0)) = k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_19]),c_0_20])])).

cnf(c_0_34,negated_conjecture,
    ( esk7_0 != k2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk6_0),X1),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_37,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),X1)) = X1
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_17]),c_0_18]),c_0_19]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk5_2(k2_funct_1(esk6_0),esk7_0),k1_relat_1(esk7_0))
    | ~ v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),X1))) = k1_funct_1(k2_funct_1(esk6_0),X1)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0))) = esk5_2(k2_funct_1(esk6_0),esk7_0)
    | ~ v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk5_2(X1,X2)) != k1_funct_1(X2,esk5_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0)))) = k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0))
    | ~ v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0))) = esk5_2(k2_funct_1(esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_12]),c_0_19]),c_0_20])])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk7_0
    | k1_funct_1(X1,esk5_2(X1,esk7_0)) != k1_funct_1(esk7_0,esk5_2(X1,esk7_0))
    | k1_relat_1(X1) != k1_relat_1(esk7_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_25])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0)) = k1_funct_1(esk7_0,esk5_2(k2_funct_1(esk6_0),esk7_0))
    | ~ v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( k2_funct_1(X1) = esk7_0
    | k1_funct_1(k2_funct_1(X1),esk5_2(k2_funct_1(X1),esk7_0)) != k1_funct_1(esk7_0,esk5_2(k2_funct_1(X1),esk7_0))
    | k1_relat_1(k2_funct_1(X1)) != k1_relat_1(esk7_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_12]),c_0_11])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0)) = k1_funct_1(esk7_0,esk5_2(k2_funct_1(esk6_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_12]),c_0_19]),c_0_20])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_19]),c_0_47]),c_0_32]),c_0_20])]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:19:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04AI
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t60_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((((v2_funct_1(X1)&k1_relat_1(X1)=k2_relat_1(X2))&k2_relat_1(X1)=k1_relat_1(X2))&![X3, X4]:((r2_hidden(X3,k1_relat_1(X1))&r2_hidden(X4,k1_relat_1(X2)))=>(k1_funct_1(X1,X3)=X4<=>k1_funct_1(X2,X4)=X3)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_funct_1)).
% 0.19/0.38  fof(t54_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k2_funct_1(X1)<=>(k1_relat_1(X2)=k2_relat_1(X1)&![X3, X4]:(((r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))=>(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4)))&((r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))=>(r2_hidden(X3,k2_relat_1(X1))&X4=k1_funct_1(X2,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_funct_1)).
% 0.19/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.38  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.19/0.38  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.38  fof(t57_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 0.19/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((((v2_funct_1(X1)&k1_relat_1(X1)=k2_relat_1(X2))&k2_relat_1(X1)=k1_relat_1(X2))&![X3, X4]:((r2_hidden(X3,k1_relat_1(X1))&r2_hidden(X4,k1_relat_1(X2)))=>(k1_funct_1(X1,X3)=X4<=>k1_funct_1(X2,X4)=X3)))=>X2=k2_funct_1(X1))))), inference(assume_negation,[status(cth)],[t60_funct_1])).
% 0.19/0.38  fof(c_0_7, plain, ![X6, X7, X8, X9, X10, X11]:(((k1_relat_1(X7)=k2_relat_1(X6)|X7!=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(((r2_hidden(X9,k1_relat_1(X6))|(~r2_hidden(X8,k2_relat_1(X6))|X9!=k1_funct_1(X7,X8))|X7!=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(X8=k1_funct_1(X6,X9)|(~r2_hidden(X8,k2_relat_1(X6))|X9!=k1_funct_1(X7,X8))|X7!=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&((r2_hidden(X10,k2_relat_1(X6))|(~r2_hidden(X11,k1_relat_1(X6))|X10!=k1_funct_1(X6,X11))|X7!=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(X11=k1_funct_1(X7,X10)|(~r2_hidden(X11,k1_relat_1(X6))|X10!=k1_funct_1(X6,X11))|X7!=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))))&(((((r2_hidden(esk4_2(X6,X7),k1_relat_1(X6))|r2_hidden(esk1_2(X6,X7),k2_relat_1(X6))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(esk3_2(X6,X7)=k1_funct_1(X6,esk4_2(X6,X7))|r2_hidden(esk1_2(X6,X7),k2_relat_1(X6))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(~r2_hidden(esk3_2(X6,X7),k2_relat_1(X6))|esk4_2(X6,X7)!=k1_funct_1(X7,esk3_2(X6,X7))|r2_hidden(esk1_2(X6,X7),k2_relat_1(X6))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(((r2_hidden(esk4_2(X6,X7),k1_relat_1(X6))|esk2_2(X6,X7)=k1_funct_1(X7,esk1_2(X6,X7))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(esk3_2(X6,X7)=k1_funct_1(X6,esk4_2(X6,X7))|esk2_2(X6,X7)=k1_funct_1(X7,esk1_2(X6,X7))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(~r2_hidden(esk3_2(X6,X7),k2_relat_1(X6))|esk4_2(X6,X7)!=k1_funct_1(X7,esk3_2(X6,X7))|esk2_2(X6,X7)=k1_funct_1(X7,esk1_2(X6,X7))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))))&(((r2_hidden(esk4_2(X6,X7),k1_relat_1(X6))|(~r2_hidden(esk2_2(X6,X7),k1_relat_1(X6))|esk1_2(X6,X7)!=k1_funct_1(X6,esk2_2(X6,X7)))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(esk3_2(X6,X7)=k1_funct_1(X6,esk4_2(X6,X7))|(~r2_hidden(esk2_2(X6,X7),k1_relat_1(X6))|esk1_2(X6,X7)!=k1_funct_1(X6,esk2_2(X6,X7)))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6))))&(~r2_hidden(esk3_2(X6,X7),k2_relat_1(X6))|esk4_2(X6,X7)!=k1_funct_1(X7,esk3_2(X6,X7))|(~r2_hidden(esk2_2(X6,X7),k1_relat_1(X6))|esk1_2(X6,X7)!=k1_funct_1(X6,esk2_2(X6,X7)))|k1_relat_1(X7)!=k2_relat_1(X6)|X7=k2_funct_1(X6)|(~v1_relat_1(X7)|~v1_funct_1(X7))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).
% 0.19/0.38  fof(c_0_8, plain, ![X5]:((v1_relat_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)))&(v1_funct_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.38  fof(c_0_9, negated_conjecture, ![X24, X25]:((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((((v2_funct_1(esk6_0)&k1_relat_1(esk6_0)=k2_relat_1(esk7_0))&k2_relat_1(esk6_0)=k1_relat_1(esk7_0))&((k1_funct_1(esk6_0,X24)!=X25|k1_funct_1(esk7_0,X25)=X24|(~r2_hidden(X24,k1_relat_1(esk6_0))|~r2_hidden(X25,k1_relat_1(esk7_0))))&(k1_funct_1(esk7_0,X25)!=X24|k1_funct_1(esk6_0,X24)=X25|(~r2_hidden(X24,k1_relat_1(esk6_0))|~r2_hidden(X25,k1_relat_1(esk7_0))))))&esk7_0!=k2_funct_1(esk6_0)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).
% 0.19/0.38  cnf(c_0_10, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(X3,k1_relat_1(X2))|X1!=k1_funct_1(X2,X3)|X4!=k2_funct_1(X2)|~v1_relat_1(X4)|~v1_funct_1(X4)|~v2_funct_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  cnf(c_0_11, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  cnf(c_0_12, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.38  fof(c_0_13, plain, ![X19, X20]:((r2_hidden(esk5_2(X19,X20),k1_relat_1(X19))|k1_relat_1(X19)!=k1_relat_1(X20)|X19=X20|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(k1_funct_1(X19,esk5_2(X19,X20))!=k1_funct_1(X20,esk5_2(X19,X20))|k1_relat_1(X19)!=k1_relat_1(X20)|X19=X20|(~v1_relat_1(X20)|~v1_funct_1(X20))|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X16]:((k2_relat_1(X16)=k1_relat_1(k2_funct_1(X16))|~v2_funct_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(k1_relat_1(X16)=k2_relat_1(k2_funct_1(X16))|~v2_funct_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (k1_funct_1(esk7_0,X2)=X1|k1_funct_1(esk6_0,X1)!=X2|~r2_hidden(X1,k1_relat_1(esk6_0))|~r2_hidden(X2,k1_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_16, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_10])]), c_0_11]), c_0_12])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (k2_relat_1(esk6_0)=k1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_21, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X3,k2_relat_1(X2))|X1!=k1_funct_1(X4,X3)|X4!=k2_funct_1(X2)|~v1_relat_1(X4)|~v1_funct_1(X4)|~v2_funct_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.38  fof(c_0_22, plain, ![X17, X18]:((X17=k1_funct_1(X18,k1_funct_1(k2_funct_1(X18),X17))|(~v2_funct_1(X18)|~r2_hidden(X17,k2_relat_1(X18)))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(X17=k1_funct_1(k5_relat_1(k2_funct_1(X18),X18),X17)|(~v2_funct_1(X18)|~r2_hidden(X17,k2_relat_1(X18)))|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_funct_1])])])).
% 0.19/0.38  cnf(c_0_23, plain, (r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_26, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))=X1|~r2_hidden(k1_funct_1(esk6_0,X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,X1),k1_relat_1(esk7_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_hidden(k1_funct_1(k2_funct_1(X1),X2),k1_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])]), c_0_11]), c_0_12])).
% 0.19/0.38  cnf(c_0_30, plain, (X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))|~v2_funct_1(X2)|~r2_hidden(X1,k2_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (X1=esk7_0|r2_hidden(esk5_2(X1,esk7_0),k1_relat_1(X1))|k1_relat_1(X1)!=k1_relat_1(esk7_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (k1_relat_1(k2_funct_1(esk6_0))=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (esk7_0!=k2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk6_0,X1))=X1|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk6_0),X1),k1_relat_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),X1))=X1|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_17]), c_0_18]), c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk5_2(k2_funct_1(esk6_0),esk7_0),k1_relat_1(esk7_0))|~v1_funct_1(k2_funct_1(esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), c_0_34])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),X1)))=k1_funct_1(k2_funct_1(esk6_0),X1)|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0)))=esk5_2(k2_funct_1(esk6_0),esk7_0)|~v1_funct_1(k2_funct_1(esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.38  cnf(c_0_41, plain, (X1=X2|k1_funct_1(X1,esk5_2(X1,X2))!=k1_funct_1(X2,esk5_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0))))=k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0))|~v1_funct_1(k2_funct_1(esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0)))=esk5_2(k2_funct_1(esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_12]), c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (X1=esk7_0|k1_funct_1(X1,esk5_2(X1,esk7_0))!=k1_funct_1(esk7_0,esk5_2(X1,esk7_0))|k1_relat_1(X1)!=k1_relat_1(esk7_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_24]), c_0_25])])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0))=k1_funct_1(esk7_0,esk5_2(k2_funct_1(esk6_0),esk7_0))|~v1_funct_1(k2_funct_1(esk6_0))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (k2_funct_1(X1)=esk7_0|k1_funct_1(k2_funct_1(X1),esk5_2(k2_funct_1(X1),esk7_0))!=k1_funct_1(esk7_0,esk5_2(k2_funct_1(X1),esk7_0))|k1_relat_1(k2_funct_1(X1))!=k1_relat_1(esk7_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_12]), c_0_11])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),esk5_2(k2_funct_1(esk6_0),esk7_0))=k1_funct_1(esk7_0,esk5_2(k2_funct_1(esk6_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_12]), c_0_19]), c_0_20])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_19]), c_0_47]), c_0_32]), c_0_20])]), c_0_34]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 49
% 0.19/0.38  # Proof object clause steps            : 36
% 0.19/0.38  # Proof object formula steps           : 13
% 0.19/0.38  # Proof object conjectures             : 29
% 0.19/0.38  # Proof object clause conjectures      : 26
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 16
% 0.19/0.38  # Proof object initial formulas used   : 6
% 0.19/0.38  # Proof object generating inferences   : 16
% 0.19/0.38  # Proof object simplifying inferences  : 47
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 6
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 32
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 32
% 0.19/0.38  # Processed clauses                    : 130
% 0.19/0.38  # ...of these trivial                  : 2
% 0.19/0.38  # ...subsumed                          : 3
% 0.19/0.38  # ...remaining for further processing  : 125
% 0.19/0.38  # Other redundant clauses eliminated   : 11
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 7
% 0.19/0.38  # Generated clauses                    : 103
% 0.19/0.38  # ...of the previous two non-trivial   : 92
% 0.19/0.38  # Contextual simplify-reflections      : 15
% 0.19/0.38  # Paramodulations                      : 92
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 15
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 80
% 0.19/0.38  #    Positive orientable unit clauses  : 26
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 53
% 0.19/0.38  # Current number of unprocessed clauses: 21
% 0.19/0.38  # ...number of literals in the above   : 127
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 38
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1483
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 142
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 19
% 0.19/0.38  # Unit Clause-clause subsumption calls : 243
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 111
% 0.19/0.38  # BW rewrite match successes           : 3
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 6353
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.035 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
