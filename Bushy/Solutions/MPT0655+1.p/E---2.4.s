%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t62_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:25 EDT 2019

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 208 expanded)
%              Number of clauses        :   24 (  72 expanded)
%              Number of leaves         :    5 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  266 (1080 expanded)
%              Number of equality atoms :   68 ( 143 expanded)
%              Maximal formula depth    :   31 (   5 average)
%              Maximal clause size      :  130 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',t62_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',dt_k2_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',t54_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',d8_funct_1)).

fof(t57_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t62_funct_1.p',t57_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => v2_funct_1(k2_funct_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t62_funct_1])).

fof(c_0_6,plain,(
    ! [X13] :
      ( ( v1_relat_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( v1_funct_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & ~ v2_funct_1(k2_funct_1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( k1_relat_1(X23) = k2_relat_1(X22)
        | X23 != k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(X25,k1_relat_1(X22))
        | ~ r2_hidden(X24,k2_relat_1(X22))
        | X25 != k1_funct_1(X23,X24)
        | X23 != k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X24 = k1_funct_1(X22,X25)
        | ~ r2_hidden(X24,k2_relat_1(X22))
        | X25 != k1_funct_1(X23,X24)
        | X23 != k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(X26,k2_relat_1(X22))
        | ~ r2_hidden(X27,k1_relat_1(X22))
        | X26 != k1_funct_1(X22,X27)
        | X23 != k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( X27 = k1_funct_1(X23,X26)
        | ~ r2_hidden(X27,k1_relat_1(X22))
        | X26 != k1_funct_1(X22,X27)
        | X23 != k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk8_2(X22,X23),k1_relat_1(X22))
        | r2_hidden(esk5_2(X22,X23),k2_relat_1(X22))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( esk7_2(X22,X23) = k1_funct_1(X22,esk8_2(X22,X23))
        | r2_hidden(esk5_2(X22,X23),k2_relat_1(X22))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk7_2(X22,X23),k2_relat_1(X22))
        | esk8_2(X22,X23) != k1_funct_1(X23,esk7_2(X22,X23))
        | r2_hidden(esk5_2(X22,X23),k2_relat_1(X22))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk8_2(X22,X23),k1_relat_1(X22))
        | esk6_2(X22,X23) = k1_funct_1(X23,esk5_2(X22,X23))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( esk7_2(X22,X23) = k1_funct_1(X22,esk8_2(X22,X23))
        | esk6_2(X22,X23) = k1_funct_1(X23,esk5_2(X22,X23))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk7_2(X22,X23),k2_relat_1(X22))
        | esk8_2(X22,X23) != k1_funct_1(X23,esk7_2(X22,X23))
        | esk6_2(X22,X23) = k1_funct_1(X23,esk5_2(X22,X23))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( r2_hidden(esk8_2(X22,X23),k1_relat_1(X22))
        | ~ r2_hidden(esk6_2(X22,X23),k1_relat_1(X22))
        | esk5_2(X22,X23) != k1_funct_1(X22,esk6_2(X22,X23))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( esk7_2(X22,X23) = k1_funct_1(X22,esk8_2(X22,X23))
        | ~ r2_hidden(esk6_2(X22,X23),k1_relat_1(X22))
        | esk5_2(X22,X23) != k1_funct_1(X22,esk6_2(X22,X23))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( ~ r2_hidden(esk7_2(X22,X23),k2_relat_1(X22))
        | esk8_2(X22,X23) != k1_funct_1(X23,esk7_2(X22,X23))
        | ~ r2_hidden(esk6_2(X22,X23),k1_relat_1(X22))
        | esk5_2(X22,X23) != k1_funct_1(X22,esk6_2(X22,X23))
        | k1_relat_1(X23) != k2_relat_1(X22)
        | X23 = k2_funct_1(X22)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23)
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_funct_1])])])])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v2_funct_1(X8)
        | ~ r2_hidden(X9,k1_relat_1(X8))
        | ~ r2_hidden(X10,k1_relat_1(X8))
        | k1_funct_1(X8,X9) != k1_funct_1(X8,X10)
        | X9 = X10
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk2_1(X8),k1_relat_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( r2_hidden(esk3_1(X8),k1_relat_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( k1_funct_1(X8,esk2_1(X8)) = k1_funct_1(X8,esk3_1(X8))
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( esk2_1(X8) != esk3_1(X8)
        | v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_10,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( k1_relat_1(X1) = k2_relat_1(X2)
    | X1 != k2_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_12])])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_funct_1(k2_funct_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( k1_relat_1(k2_funct_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_13]),c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_22,plain,(
    ! [X32,X33] :
      ( ( X32 = k1_funct_1(X33,k1_funct_1(k2_funct_1(X33),X32))
        | ~ v2_funct_1(X33)
        | ~ r2_hidden(X32,k2_relat_1(X33))
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( X32 = k1_funct_1(k5_relat_1(k2_funct_1(X33),X33),X32)
        | ~ v2_funct_1(X33)
        | ~ r2_hidden(X32,k2_relat_1(X33))
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_funct_1])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk3_1(k2_funct_1(esk1_0)),k1_relat_1(k2_funct_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk1_0)) = k2_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_20]),c_0_12])])).

cnf(c_0_25,plain,
    ( k1_funct_1(X1,esk2_1(X1)) = k1_funct_1(X1,esk3_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_1(k2_funct_1(esk1_0)),k1_relat_1(k2_funct_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_27,plain,
    ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk3_1(k2_funct_1(esk1_0)),k2_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk1_0),esk3_1(k2_funct_1(esk1_0))) = k1_funct_1(k2_funct_1(esk1_0),esk2_1(k2_funct_1(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_1(k2_funct_1(esk1_0)),k2_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k1_funct_1(esk1_0,k1_funct_1(k2_funct_1(esk1_0),esk2_1(k2_funct_1(esk1_0)))) = esk3_1(k2_funct_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20]),c_0_11]),c_0_12])]),c_0_29])).

cnf(c_0_32,plain,
    ( v2_funct_1(X1)
    | esk2_1(X1) != esk3_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( esk3_1(k2_funct_1(esk1_0)) = esk2_1(k2_funct_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_30]),c_0_20]),c_0_11]),c_0_12])]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_16]),c_0_17])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
