%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0655+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:58 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 179 expanded)
%              Number of clauses        :   26 (  61 expanded)
%              Number of leaves         :    5 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  278 (1007 expanded)
%              Number of equality atoms :   68 ( 142 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t62_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

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

fof(t57_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(c_0_5,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v2_funct_1(X5)
        | ~ r2_hidden(X6,k1_relat_1(X5))
        | ~ r2_hidden(X7,k1_relat_1(X5))
        | k1_funct_1(X5,X6) != k1_funct_1(X5,X7)
        | X6 = X7
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(esk1_1(X5),k1_relat_1(X5))
        | v2_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( r2_hidden(esk2_1(X5),k1_relat_1(X5))
        | v2_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( k1_funct_1(X5,esk1_1(X5)) = k1_funct_1(X5,esk2_1(X5))
        | v2_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( esk1_1(X5) != esk2_1(X5)
        | v2_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

fof(c_0_6,plain,(
    ! [X10] :
      ( ( v1_relat_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( v1_funct_1(k2_funct_1(X10))
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k2_funct_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_1])).

cnf(c_0_8,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v2_funct_1(esk7_0)
    & ~ v2_funct_1(k2_funct_1(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_12,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( k1_relat_1(X12) = k2_relat_1(X11)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(X14,k1_relat_1(X11))
        | ~ r2_hidden(X13,k2_relat_1(X11))
        | X14 != k1_funct_1(X12,X13)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X13 = k1_funct_1(X11,X14)
        | ~ r2_hidden(X13,k2_relat_1(X11))
        | X14 != k1_funct_1(X12,X13)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(X15,k2_relat_1(X11))
        | ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X16 = k1_funct_1(X12,X15)
        | ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | X12 != k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_2(X11,X12),k1_relat_1(X11))
        | r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk5_2(X11,X12) = k1_funct_1(X11,esk6_2(X11,X12))
        | r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk5_2(X11,X12),k2_relat_1(X11))
        | esk6_2(X11,X12) != k1_funct_1(X12,esk5_2(X11,X12))
        | r2_hidden(esk3_2(X11,X12),k2_relat_1(X11))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_2(X11,X12),k1_relat_1(X11))
        | esk4_2(X11,X12) = k1_funct_1(X12,esk3_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk5_2(X11,X12) = k1_funct_1(X11,esk6_2(X11,X12))
        | esk4_2(X11,X12) = k1_funct_1(X12,esk3_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk5_2(X11,X12),k2_relat_1(X11))
        | esk6_2(X11,X12) != k1_funct_1(X12,esk5_2(X11,X12))
        | esk4_2(X11,X12) = k1_funct_1(X12,esk3_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk6_2(X11,X12),k1_relat_1(X11))
        | ~ r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))
        | esk3_2(X11,X12) != k1_funct_1(X11,esk4_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk5_2(X11,X12) = k1_funct_1(X11,esk6_2(X11,X12))
        | ~ r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))
        | esk3_2(X11,X12) != k1_funct_1(X11,esk4_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk5_2(X11,X12),k2_relat_1(X11))
        | esk6_2(X11,X12) != k1_funct_1(X12,esk5_2(X11,X12))
        | ~ r2_hidden(esk4_2(X11,X12),k1_relat_1(X11))
        | esk3_2(X11,X12) != k1_funct_1(X11,esk4_2(X11,X12))
        | k1_relat_1(X12) != k2_relat_1(X11)
        | X12 = k2_funct_1(X11)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

cnf(c_0_13,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_1(k2_funct_1(X1)),k1_relat_1(k2_funct_1(X1)))
    | v2_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k1_relat_1(X1) = k2_relat_1(X2)
    | X1 != k2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_20,plain,(
    ! [X21,X22] :
      ( ( X21 = k1_funct_1(X22,k1_funct_1(k2_funct_1(X22),X21))
        | ~ v2_funct_1(X22)
        | ~ r2_hidden(X21,k2_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X21 = k1_funct_1(k5_relat_1(k2_funct_1(X22),X22),X21)
        | ~ v2_funct_1(X22)
        | ~ r2_hidden(X21,k2_relat_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_funct_1])])])).

cnf(c_0_21,plain,
    ( k1_funct_1(k2_funct_1(X1),esk2_1(k2_funct_1(X1))) = k1_funct_1(k2_funct_1(X1),esk1_1(k2_funct_1(X1)))
    | v2_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_9]),c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_1(k2_funct_1(esk7_0)),k1_relat_1(k2_funct_1(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_23,plain,
    ( k1_relat_1(k2_funct_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_18]),c_0_10]),c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_1(k2_funct_1(X1)),k1_relat_1(k2_funct_1(X1)))
    | v2_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_9]),c_0_10])).

cnf(c_0_26,plain,
    ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk7_0),esk2_1(k2_funct_1(esk7_0))) = k1_funct_1(k2_funct_1(esk7_0),esk1_1(k2_funct_1(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_1(k2_funct_1(esk7_0)),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_15]),c_0_16])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_1(k2_funct_1(esk7_0)),k1_relat_1(k2_funct_1(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk1_1(k2_funct_1(esk7_0)))) = esk2_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_24]),c_0_15]),c_0_16])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_1(k2_funct_1(esk7_0)),k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_24]),c_0_15]),c_0_16])])).

cnf(c_0_32,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_33,negated_conjecture,
    ( esk2_1(k2_funct_1(esk7_0)) = esk1_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_30]),c_0_31]),c_0_24]),c_0_15]),c_0_16])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_9]),c_0_15]),c_0_16])])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_10]),c_0_15]),c_0_16])]),
    [proof]).

%------------------------------------------------------------------------------
