%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0653+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (14758 expanded)
%              Number of clauses        :   57 (4694 expanded)
%              Number of leaves         :    3 (3514 expanded)
%              Depth                    :   19
%              Number of atoms          :  426 (187211 expanded)
%              Number of equality atoms :  161 (73960 expanded)
%              Maximal formula depth    :   31 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_1)).

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

fof(c_0_4,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( k1_relat_1(X16) = k2_relat_1(X15)
        | X16 != k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(X18,k1_relat_1(X15))
        | ~ r2_hidden(X17,k2_relat_1(X15))
        | X18 != k1_funct_1(X16,X17)
        | X16 != k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X17 = k1_funct_1(X15,X18)
        | ~ r2_hidden(X17,k2_relat_1(X15))
        | X18 != k1_funct_1(X16,X17)
        | X16 != k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(X19,k2_relat_1(X15))
        | ~ r2_hidden(X20,k1_relat_1(X15))
        | X19 != k1_funct_1(X15,X20)
        | X16 != k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X20 = k1_funct_1(X16,X19)
        | ~ r2_hidden(X20,k1_relat_1(X15))
        | X19 != k1_funct_1(X15,X20)
        | X16 != k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk7_2(X15,X16),k1_relat_1(X15))
        | r2_hidden(esk4_2(X15,X16),k2_relat_1(X15))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk6_2(X15,X16) = k1_funct_1(X15,esk7_2(X15,X16))
        | r2_hidden(esk4_2(X15,X16),k2_relat_1(X15))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk6_2(X15,X16),k2_relat_1(X15))
        | esk7_2(X15,X16) != k1_funct_1(X16,esk6_2(X15,X16))
        | r2_hidden(esk4_2(X15,X16),k2_relat_1(X15))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk7_2(X15,X16),k1_relat_1(X15))
        | esk5_2(X15,X16) = k1_funct_1(X16,esk4_2(X15,X16))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk6_2(X15,X16) = k1_funct_1(X15,esk7_2(X15,X16))
        | esk5_2(X15,X16) = k1_funct_1(X16,esk4_2(X15,X16))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk6_2(X15,X16),k2_relat_1(X15))
        | esk7_2(X15,X16) != k1_funct_1(X16,esk6_2(X15,X16))
        | esk5_2(X15,X16) = k1_funct_1(X16,esk4_2(X15,X16))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk7_2(X15,X16),k1_relat_1(X15))
        | ~ r2_hidden(esk5_2(X15,X16),k1_relat_1(X15))
        | esk4_2(X15,X16) != k1_funct_1(X15,esk5_2(X15,X16))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( esk6_2(X15,X16) = k1_funct_1(X15,esk7_2(X15,X16))
        | ~ r2_hidden(esk5_2(X15,X16),k1_relat_1(X15))
        | esk4_2(X15,X16) != k1_funct_1(X15,esk5_2(X15,X16))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk6_2(X15,X16),k2_relat_1(X15))
        | esk7_2(X15,X16) != k1_funct_1(X16,esk6_2(X15,X16))
        | ~ r2_hidden(esk5_2(X15,X16),k1_relat_1(X15))
        | esk4_2(X15,X16) != k1_funct_1(X15,esk5_2(X15,X16))
        | k1_relat_1(X16) != k2_relat_1(X15)
        | X16 = k2_funct_1(X15)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X27,X28] :
      ( v1_relat_1(esk8_0)
      & v1_funct_1(esk8_0)
      & v1_relat_1(esk9_0)
      & v1_funct_1(esk9_0)
      & v2_funct_1(esk8_0)
      & k1_relat_1(esk8_0) = k2_relat_1(esk9_0)
      & k2_relat_1(esk8_0) = k1_relat_1(esk9_0)
      & ( k1_funct_1(esk8_0,X27) != X28
        | k1_funct_1(esk9_0,X28) = X27
        | ~ r2_hidden(X27,k1_relat_1(esk8_0))
        | ~ r2_hidden(X28,k1_relat_1(esk9_0)) )
      & ( k1_funct_1(esk9_0,X28) != X27
        | k1_funct_1(esk8_0,X27) = X28
        | ~ r2_hidden(X27,k1_relat_1(esk8_0))
        | ~ r2_hidden(X28,k1_relat_1(esk9_0)) )
      & esk9_0 != k2_funct_1(esk8_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])])])).

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

cnf(c_0_7,plain,
    ( esk6_2(X1,X2) = k1_funct_1(X1,esk7_2(X1,X2))
    | r2_hidden(esk4_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,negated_conjecture,
    ( v2_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( k2_relat_1(esk8_0) = k1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_2(esk8_0,X1)) = esk6_2(esk8_0,X1)
    | X1 = k2_funct_1(esk8_0)
    | r2_hidden(esk4_2(esk8_0,X1),k1_relat_1(esk9_0))
    | k1_relat_1(X1) != k1_relat_1(esk9_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_16,negated_conjecture,
    ( esk9_0 != k2_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_17,plain,
    ( esk6_2(X1,X2) = k1_funct_1(X1,esk7_2(X1,X2))
    | esk5_2(X1,X2) = k1_funct_1(X2,esk4_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

cnf(c_0_19,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)) = esk6_2(esk8_0,esk9_0)
    | r2_hidden(esk4_2(esk8_0,esk9_0),k1_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( k1_relat_1(esk8_0) = k2_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_2(esk8_0,X1)) = esk6_2(esk8_0,X1)
    | k1_funct_1(X1,esk4_2(esk8_0,X1)) = esk5_2(esk8_0,X1)
    | X1 = k2_funct_1(esk8_0)
    | k1_relat_1(X1) != k1_relat_1(esk9_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_8]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk7_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk4_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(esk8_0,X2) = X1
    | k1_funct_1(esk9_0,X1) != X2
    | ~ r2_hidden(X2,k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)) = esk6_2(esk8_0,esk9_0)
    | r2_hidden(k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_14]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0)
    | k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)) = esk6_2(esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( X1 = k2_funct_1(esk8_0)
    | r2_hidden(esk7_2(esk8_0,X1),k1_relat_1(esk8_0))
    | r2_hidden(esk4_2(esk8_0,X1),k1_relat_1(esk9_0))
    | k1_relat_1(X1) != k1_relat_1(esk9_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_8]),c_0_9]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk9_0,X1)) = X1
    | ~ r2_hidden(k1_funct_1(esk9_0,X1),k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k1_relat_1(esk9_0)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( esk6_2(X1,X2) = k1_funct_1(X1,esk7_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X1,esk5_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_29,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)) = esk6_2(esk8_0,esk9_0)
    | r2_hidden(esk5_2(esk8_0,esk9_0),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(esk7_2(X1,X2),k1_relat_1(X1))
    | esk5_2(X1,X2) = k1_funct_1(X2,esk4_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k1_relat_1(esk9_0))
    | r2_hidden(esk7_2(esk8_0,esk9_0),k1_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0))) = esk4_2(esk8_0,esk9_0)
    | k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)) = esk6_2(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_24]),c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)) = esk6_2(esk8_0,esk9_0)
    | k1_funct_1(esk8_0,esk5_2(esk8_0,esk9_0)) != esk4_2(esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_9]),c_0_8]),c_0_14]),c_0_10]),c_0_15]),c_0_11])]),c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(X1,esk4_2(esk8_0,X1)) = esk5_2(esk8_0,X1)
    | X1 = k2_funct_1(esk8_0)
    | r2_hidden(esk7_2(esk8_0,X1),k1_relat_1(esk8_0))
    | k1_relat_1(X1) != k1_relat_1(esk9_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_8]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_35,negated_conjecture,
    ( k1_funct_1(esk9_0,X2) = X1
    | k1_funct_1(esk8_0,X1) != X2
    | ~ r2_hidden(X1,k1_relat_1(esk8_0))
    | ~ r2_hidden(X2,k1_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_36,plain,
    ( r2_hidden(esk4_2(X1,X2),k2_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),k2_relat_1(X1))
    | esk7_2(X1,X2) != k1_funct_1(X2,esk6_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)),k1_relat_1(esk9_0))
    | r2_hidden(esk4_2(esk8_0,esk9_0),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_31]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)) = esk6_2(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0)
    | r2_hidden(esk7_2(esk8_0,esk9_0),k1_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,X1)) = X1
    | ~ r2_hidden(k1_funct_1(esk8_0,X1),k1_relat_1(esk9_0))
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k2_funct_1(esk8_0)
    | r2_hidden(esk4_2(esk8_0,X1),k1_relat_1(esk9_0))
    | k1_funct_1(X1,esk6_2(esk8_0,X1)) != esk7_2(esk8_0,X1)
    | k1_relat_1(X1) != k1_relat_1(esk9_0)
    | ~ r2_hidden(esk6_2(esk8_0,X1),k1_relat_1(esk9_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_9]),c_0_8]),c_0_10]),c_0_11])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k1_relat_1(esk9_0))
    | r2_hidden(esk6_2(esk8_0,esk9_0),k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( esk5_2(X1,X2) = k1_funct_1(X2,esk4_2(X1,X2))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),k2_relat_1(X1))
    | esk7_2(X1,X2) != k1_funct_1(X2,esk6_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_44,negated_conjecture,
    ( k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0)
    | r2_hidden(k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0)),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_39]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_45,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0))) = esk7_2(esk8_0,esk9_0)
    | r2_hidden(esk4_2(esk8_0,esk9_0),k1_relat_1(esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k1_relat_1(esk9_0))
    | k1_funct_1(esk9_0,esk6_2(esk8_0,esk9_0)) != esk7_2(esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(X1,esk4_2(esk8_0,X1)) = esk5_2(esk8_0,X1)
    | X1 = k2_funct_1(esk8_0)
    | k1_funct_1(X1,esk6_2(esk8_0,X1)) != esk7_2(esk8_0,X1)
    | k1_relat_1(X1) != k1_relat_1(esk9_0)
    | ~ r2_hidden(esk6_2(esk8_0,X1),k1_relat_1(esk9_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_9]),c_0_8]),c_0_10]),c_0_11])])).

cnf(c_0_48,negated_conjecture,
    ( k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0)
    | r2_hidden(esk6_2(esk8_0,esk9_0),k1_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,esk9_0),k1_relat_1(esk9_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_38]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( k1_funct_1(esk9_0,k1_funct_1(esk8_0,esk7_2(esk8_0,esk9_0))) = esk7_2(esk8_0,esk9_0)
    | k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_44]),c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0)
    | k1_funct_1(esk9_0,esk6_2(esk8_0,esk9_0)) != esk7_2(esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_49]),c_0_20]),c_0_14]),c_0_15])])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0)) = esk5_2(esk8_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_38]),c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(esk9_0,esk4_2(esk8_0,esk9_0))) = esk4_2(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_52]),c_0_49])])).

cnf(c_0_55,plain,
    ( r2_hidden(esk7_2(X1,X2),k1_relat_1(X1))
    | X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X1,esk5_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_2(esk8_0,esk9_0),k1_relat_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k1_funct_1(esk8_0,esk5_2(esk8_0,esk9_0)) = esk4_2(esk8_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk7_2(esk8_0,esk9_0),k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_9]),c_0_8]),c_0_14]),c_0_10]),c_0_15]),c_0_11])]),c_0_16]),c_0_57])])).

cnf(c_0_59,plain,
    ( X2 = k2_funct_1(X1)
    | ~ r2_hidden(esk6_2(X1,X2),k2_relat_1(X1))
    | esk7_2(X1,X2) != k1_funct_1(X2,esk6_2(X1,X2))
    | ~ r2_hidden(esk5_2(X1,X2),k1_relat_1(X1))
    | esk4_2(X1,X2) != k1_funct_1(X1,esk5_2(X1,X2))
    | k1_relat_1(X2) != k2_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_2(esk8_0,esk9_0),k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_58]),c_0_38]),c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_61,negated_conjecture,
    ( k1_funct_1(esk9_0,esk6_2(esk8_0,esk9_0)) = esk7_2(esk8_0,esk9_0)
    | ~ r2_hidden(esk6_2(esk8_0,esk9_0),k1_relat_1(esk9_0))
    | ~ r2_hidden(esk7_2(esk8_0,esk9_0),k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk9_0,esk6_2(esk8_0,esk9_0)) != esk7_2(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_56]),c_0_9]),c_0_8]),c_0_9]),c_0_14]),c_0_10]),c_0_15]),c_0_11])]),c_0_16]),c_0_57]),c_0_60])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_58])]),c_0_60])]),c_0_62]),
    [proof]).

%------------------------------------------------------------------------------
