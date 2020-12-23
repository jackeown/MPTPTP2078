%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 397 expanded)
%              Number of clauses        :   54 ( 153 expanded)
%              Number of leaves         :   11 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :  321 (2218 expanded)
%              Number of equality atoms :   96 ( 624 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

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

fof(c_0_11,plain,(
    ! [X9,X10,X11,X13,X14,X15,X17] :
      ( ( r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X9))
        | ~ r2_hidden(X11,X10)
        | X10 != k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( X11 = k1_funct_1(X9,esk1_3(X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(X14,k1_relat_1(X9))
        | X13 != k1_funct_1(X9,X14)
        | r2_hidden(X13,X10)
        | X10 != k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(esk2_2(X9,X15),X15)
        | ~ r2_hidden(X17,k1_relat_1(X9))
        | esk2_2(X9,X15) != k1_funct_1(X9,X17)
        | X15 = k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk3_2(X9,X15),k1_relat_1(X9))
        | r2_hidden(esk2_2(X9,X15),X15)
        | X15 = k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk2_2(X9,X15) = k1_funct_1(X9,esk3_2(X9,X15))
        | r2_hidden(esk2_2(X9,X15),X15)
        | X15 = k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_12,plain,(
    ! [X20] :
      ( ( v1_relat_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( v1_funct_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_14,plain,(
    ! [X29,X30] :
      ( ( X29 = k1_funct_1(k2_funct_1(X30),k1_funct_1(X30,X29))
        | ~ v2_funct_1(X30)
        | ~ r2_hidden(X29,k1_relat_1(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( X29 = k1_funct_1(k5_relat_1(X30,k2_funct_1(X30)),X29)
        | ~ v2_funct_1(X30)
        | ~ r2_hidden(X29,k1_relat_1(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_15,plain,
    ( X1 = k1_funct_1(X2,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v2_funct_1(esk6_0)
    & r2_hidden(esk5_0,k2_relat_1(esk6_0))
    & ( esk5_0 != k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))
      | esk5_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_21,plain,(
    ! [X7] :
      ( ( k2_relat_1(X7) = k1_relat_1(k4_relat_1(X7))
        | ~ v1_relat_1(X7) )
      & ( k1_relat_1(X7) = k2_relat_1(k4_relat_1(X7))
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_22,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ v2_funct_1(X19)
      | k2_funct_1(X19) = k4_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_23,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( esk2_2(X1,X2) = k1_funct_1(X1,esk3_2(X1,X2))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,plain,
    ( X1 = k2_relat_1(k2_funct_1(X2))
    | r2_hidden(esk3_2(k2_funct_1(X2),X1),k1_relat_1(k2_funct_1(X2)))
    | r2_hidden(esk2_2(k2_funct_1(X2),X1),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( esk1_3(X1,k2_relat_1(X1),X2) = k1_funct_1(k2_funct_1(X1),X2)
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_33,plain,
    ( k1_funct_1(k2_funct_1(X1),esk3_2(k2_funct_1(X1),X2)) = esk2_2(k2_funct_1(X1),X2)
    | X2 = k2_relat_1(k2_funct_1(X1))
    | r2_hidden(esk2_2(k2_funct_1(X1),X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_18]),c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( X1 = k2_relat_1(k2_funct_1(esk6_0))
    | r2_hidden(esk3_2(k2_funct_1(esk6_0),X1),k1_relat_1(k2_funct_1(esk6_0)))
    | r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_35,plain,
    ( k1_relat_1(k2_funct_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(X1),X2),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk6_0),esk3_2(k2_funct_1(esk6_0),X1)) = esk2_2(k2_funct_1(esk6_0),X1)
    | X1 = k2_relat_1(k2_funct_1(esk6_0))
    | r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( X1 = k2_relat_1(k2_funct_1(esk6_0))
    | r2_hidden(esk3_2(k2_funct_1(esk6_0),X1),k2_relat_1(esk6_0))
    | r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_28]),c_0_29])])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k2_relat_1(k2_funct_1(esk6_0))
    | r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),k1_relat_1(esk6_0))
    | r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_36]),c_0_28]),c_0_29])]),c_0_39])).

cnf(c_0_41,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | esk2_2(X1,X2) != k1_funct_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk6_0)) = k1_relat_1(esk6_0)
    | r2_hidden(esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(ef,[status(thm)],[c_0_40])).

fof(c_0_43,plain,(
    ! [X25,X26,X27] :
      ( ( k1_relat_1(X26) = X25
        | X26 != k6_relat_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X27,X25)
        | k1_funct_1(X26,X27) = X27
        | X26 != k6_relat_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(esk4_2(X25,X26),X25)
        | k1_relat_1(X26) != X25
        | X26 = k6_relat_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( k1_funct_1(X26,esk4_2(X25,X26)) != esk4_2(X25,X26)
        | k1_relat_1(X26) != X25
        | X26 = k6_relat_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_44,plain,(
    ! [X21] :
      ( v1_relat_1(k6_relat_1(X21))
      & v1_funct_1(k6_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_45,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk6_0)) = k1_relat_1(esk6_0)
    | esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0)) != k1_funct_1(k2_funct_1(esk6_0),X1)
    | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0)))
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_47,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | k1_relat_1(k5_relat_1(X5,X6)) = k10_relat_1(X5,k1_relat_1(X6)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_48,plain,
    ( k1_relat_1(X1) = X2
    | X1 != k6_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk6_0)) = k1_relat_1(esk6_0)
    | esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0)) != k1_funct_1(k2_funct_1(esk6_0),X1)
    | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0)))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_18]),c_0_28]),c_0_29])])).

cnf(c_0_52,plain,
    ( k2_relat_1(k2_funct_1(X1)) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_53,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49]),c_0_50])])).

fof(c_0_55,plain,(
    ! [X8] :
      ( ~ v1_relat_1(X8)
      | k5_relat_1(X8,k6_relat_1(k2_relat_1(X8))) = X8 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk6_0)) = k1_relat_1(esk6_0)
    | esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0)) != k1_funct_1(k2_funct_1(esk6_0),X1)
    | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_28]),c_0_29])])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_3(k2_funct_1(X1),k1_relat_1(X1),X2),k1_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_52]),c_0_19]),c_0_18])).

cnf(c_0_58,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_50])])).

cnf(c_0_59,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk6_0)) = k1_relat_1(esk6_0)
    | k1_funct_1(k2_funct_1(esk6_0),esk1_3(k2_funct_1(esk6_0),k1_relat_1(esk6_0),X1)) != esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_36]),c_0_28]),c_0_29])])).

cnf(c_0_61,plain,
    ( k1_funct_1(k2_funct_1(X1),esk1_3(k2_funct_1(X1),k1_relat_1(X1),X2)) = X2
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_52]),c_0_19]),c_0_18])).

cnf(c_0_62,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk6_0)) = k1_relat_1(esk6_0) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_36]),c_0_28]),c_0_29])])]),c_0_42])).

fof(c_0_64,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ r2_hidden(X22,k1_relat_1(k5_relat_1(X24,X23)))
      | k1_funct_1(k5_relat_1(X24,X23),X22) = k1_funct_1(X23,k1_funct_1(X24,X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_65,negated_conjecture,
    ( k10_relat_1(k2_funct_1(esk6_0),k1_relat_1(esk6_0)) = k1_relat_1(k2_funct_1(esk6_0))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0)) = k1_relat_1(k2_funct_1(esk6_0))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_65]),c_0_29])])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 != k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))
    | esk5_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),X1) = k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),X1))
    | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0)))
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_28]),c_0_29])])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0)) != esk5_0
    | ~ r2_hidden(esk5_0,k1_relat_1(k2_funct_1(esk6_0)))
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_71,plain,
    ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X2)) = X2
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_32])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk5_0,k2_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_relat_1(k2_funct_1(esk6_0)))
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_36]),c_0_72]),c_0_28]),c_0_29])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_35]),c_0_72]),c_0_36]),c_0_28]),c_0_29])])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_18]),c_0_28]),c_0_29])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_19]),c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.027 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.45  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.45  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 0.20/0.45  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 0.20/0.45  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.20/0.45  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.20/0.45  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 0.20/0.45  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.45  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.20/0.45  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 0.20/0.45  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 0.20/0.45  fof(c_0_11, plain, ![X9, X10, X11, X13, X14, X15, X17]:((((r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X9))|~r2_hidden(X11,X10)|X10!=k2_relat_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(X11=k1_funct_1(X9,esk1_3(X9,X10,X11))|~r2_hidden(X11,X10)|X10!=k2_relat_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&(~r2_hidden(X14,k1_relat_1(X9))|X13!=k1_funct_1(X9,X14)|r2_hidden(X13,X10)|X10!=k2_relat_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9))))&((~r2_hidden(esk2_2(X9,X15),X15)|(~r2_hidden(X17,k1_relat_1(X9))|esk2_2(X9,X15)!=k1_funct_1(X9,X17))|X15=k2_relat_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&((r2_hidden(esk3_2(X9,X15),k1_relat_1(X9))|r2_hidden(esk2_2(X9,X15),X15)|X15=k2_relat_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))&(esk2_2(X9,X15)=k1_funct_1(X9,esk3_2(X9,X15))|r2_hidden(esk2_2(X9,X15),X15)|X15=k2_relat_1(X9)|(~v1_relat_1(X9)|~v1_funct_1(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.45  fof(c_0_12, plain, ![X20]:((v1_relat_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(v1_funct_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.45  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 0.20/0.45  fof(c_0_14, plain, ![X29, X30]:((X29=k1_funct_1(k2_funct_1(X30),k1_funct_1(X30,X29))|(~v2_funct_1(X30)|~r2_hidden(X29,k1_relat_1(X30)))|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(X29=k1_funct_1(k5_relat_1(X30,k2_funct_1(X30)),X29)|(~v2_funct_1(X30)|~r2_hidden(X29,k1_relat_1(X30)))|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.20/0.45  cnf(c_0_15, plain, (X1=k1_funct_1(X2,esk1_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  cnf(c_0_16, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  cnf(c_0_17, plain, (r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk2_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  cnf(c_0_18, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  cnf(c_0_19, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.45  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&((v2_funct_1(esk6_0)&r2_hidden(esk5_0,k2_relat_1(esk6_0)))&(esk5_0!=k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.45  fof(c_0_21, plain, ![X7]:((k2_relat_1(X7)=k1_relat_1(k4_relat_1(X7))|~v1_relat_1(X7))&(k1_relat_1(X7)=k2_relat_1(k4_relat_1(X7))|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.20/0.45  fof(c_0_22, plain, ![X19]:(~v1_relat_1(X19)|~v1_funct_1(X19)|(~v2_funct_1(X19)|k2_funct_1(X19)=k4_relat_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.20/0.45  cnf(c_0_23, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.45  cnf(c_0_24, plain, (k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2))=X2|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.45  cnf(c_0_25, plain, (r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.45  cnf(c_0_26, plain, (esk2_2(X1,X2)=k1_funct_1(X1,esk3_2(X1,X2))|r2_hidden(esk2_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  cnf(c_0_27, plain, (X1=k2_relat_1(k2_funct_1(X2))|r2_hidden(esk3_2(k2_funct_1(X2),X1),k1_relat_1(k2_funct_1(X2)))|r2_hidden(esk2_2(k2_funct_1(X2),X1),X1)|~v1_funct_1(X2)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.20/0.45  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_30, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_31, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.45  cnf(c_0_32, plain, (esk1_3(X1,k2_relat_1(X1),X2)=k1_funct_1(k2_funct_1(X1),X2)|~v2_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.20/0.45  cnf(c_0_33, plain, (k1_funct_1(k2_funct_1(X1),esk3_2(k2_funct_1(X1),X2))=esk2_2(k2_funct_1(X1),X2)|X2=k2_relat_1(k2_funct_1(X1))|r2_hidden(esk2_2(k2_funct_1(X1),X2),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_18]), c_0_19])).
% 0.20/0.45  cnf(c_0_34, negated_conjecture, (X1=k2_relat_1(k2_funct_1(esk6_0))|r2_hidden(esk3_2(k2_funct_1(esk6_0),X1),k1_relat_1(k2_funct_1(esk6_0)))|r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_35, plain, (k1_relat_1(k2_funct_1(X1))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.45  cnf(c_0_36, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_37, plain, (r2_hidden(k1_funct_1(k2_funct_1(X1),X2),k1_relat_1(X1))|~v2_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_32])).
% 0.20/0.45  cnf(c_0_38, negated_conjecture, (k1_funct_1(k2_funct_1(esk6_0),esk3_2(k2_funct_1(esk6_0),X1))=esk2_2(k2_funct_1(esk6_0),X1)|X1=k2_relat_1(k2_funct_1(esk6_0))|r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_39, negated_conjecture, (X1=k2_relat_1(k2_funct_1(esk6_0))|r2_hidden(esk3_2(k2_funct_1(esk6_0),X1),k2_relat_1(esk6_0))|r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_40, negated_conjecture, (X1=k2_relat_1(k2_funct_1(esk6_0))|r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),k1_relat_1(esk6_0))|r2_hidden(esk2_2(k2_funct_1(esk6_0),X1),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_36]), c_0_28]), c_0_29])]), c_0_39])).
% 0.20/0.45  cnf(c_0_41, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk2_2(X1,X2),X2)|~r2_hidden(X3,k1_relat_1(X1))|esk2_2(X1,X2)!=k1_funct_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.45  cnf(c_0_42, negated_conjecture, (k2_relat_1(k2_funct_1(esk6_0))=k1_relat_1(esk6_0)|r2_hidden(esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))), inference(ef,[status(thm)],[c_0_40])).
% 0.20/0.45  fof(c_0_43, plain, ![X25, X26, X27]:(((k1_relat_1(X26)=X25|X26!=k6_relat_1(X25)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(~r2_hidden(X27,X25)|k1_funct_1(X26,X27)=X27|X26!=k6_relat_1(X25)|(~v1_relat_1(X26)|~v1_funct_1(X26))))&((r2_hidden(esk4_2(X25,X26),X25)|k1_relat_1(X26)!=X25|X26=k6_relat_1(X25)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(k1_funct_1(X26,esk4_2(X25,X26))!=esk4_2(X25,X26)|k1_relat_1(X26)!=X25|X26=k6_relat_1(X25)|(~v1_relat_1(X26)|~v1_funct_1(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 0.20/0.45  fof(c_0_44, plain, ![X21]:(v1_relat_1(k6_relat_1(X21))&v1_funct_1(k6_relat_1(X21))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.45  cnf(c_0_45, negated_conjecture, (k2_relat_1(k2_funct_1(esk6_0))=k1_relat_1(esk6_0)|esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0))!=k1_funct_1(k2_funct_1(esk6_0),X1)|~r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0)))|~v1_funct_1(k2_funct_1(esk6_0))|~v1_relat_1(k2_funct_1(esk6_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.45  cnf(c_0_46, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  fof(c_0_47, plain, ![X5, X6]:(~v1_relat_1(X5)|(~v1_relat_1(X6)|k1_relat_1(k5_relat_1(X5,X6))=k10_relat_1(X5,k1_relat_1(X6)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.20/0.45  cnf(c_0_48, plain, (k1_relat_1(X1)=X2|X1!=k6_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.45  cnf(c_0_49, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_50, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.45  cnf(c_0_51, negated_conjecture, (k2_relat_1(k2_funct_1(esk6_0))=k1_relat_1(esk6_0)|esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0))!=k1_funct_1(k2_funct_1(esk6_0),X1)|~r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0)))|~v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_18]), c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_52, plain, (k2_relat_1(k2_funct_1(X1))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_31])).
% 0.20/0.45  cnf(c_0_53, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.45  cnf(c_0_54, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_49]), c_0_50])])).
% 0.20/0.45  fof(c_0_55, plain, ![X8]:(~v1_relat_1(X8)|k5_relat_1(X8,k6_relat_1(k2_relat_1(X8)))=X8), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.20/0.45  cnf(c_0_56, negated_conjecture, (k2_relat_1(k2_funct_1(esk6_0))=k1_relat_1(esk6_0)|esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0))!=k1_funct_1(k2_funct_1(esk6_0),X1)|~r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_57, plain, (r2_hidden(esk1_3(k2_funct_1(X1),k1_relat_1(X1),X2),k1_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_52]), c_0_19]), c_0_18])).
% 0.20/0.45  cnf(c_0_58, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_50])])).
% 0.20/0.45  cnf(c_0_59, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.45  cnf(c_0_60, negated_conjecture, (k2_relat_1(k2_funct_1(esk6_0))=k1_relat_1(esk6_0)|k1_funct_1(k2_funct_1(esk6_0),esk1_3(k2_funct_1(esk6_0),k1_relat_1(esk6_0),X1))!=esk2_2(k2_funct_1(esk6_0),k1_relat_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_36]), c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_61, plain, (k1_funct_1(k2_funct_1(X1),esk1_3(k2_funct_1(X1),k1_relat_1(X1),X2))=X2|~v2_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_52]), c_0_19]), c_0_18])).
% 0.20/0.45  cnf(c_0_62, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (k2_relat_1(k2_funct_1(esk6_0))=k1_relat_1(esk6_0)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_36]), c_0_28]), c_0_29])])]), c_0_42])).
% 0.20/0.45  fof(c_0_64, plain, ![X22, X23, X24]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v1_relat_1(X24)|~v1_funct_1(X24)|(~r2_hidden(X22,k1_relat_1(k5_relat_1(X24,X23)))|k1_funct_1(k5_relat_1(X24,X23),X22)=k1_funct_1(X23,k1_funct_1(X24,X22))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 0.20/0.45  cnf(c_0_65, negated_conjecture, (k10_relat_1(k2_funct_1(esk6_0),k1_relat_1(esk6_0))=k1_relat_1(k2_funct_1(esk6_0))|~v1_relat_1(k2_funct_1(esk6_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.45  cnf(c_0_66, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.20/0.45  cnf(c_0_67, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0))=k1_relat_1(k2_funct_1(esk6_0))|~v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_65]), c_0_29])])).
% 0.20/0.45  cnf(c_0_68, negated_conjecture, (esk5_0!=k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))|esk5_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_69, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(esk6_0),esk6_0),X1)=k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),X1))|~r2_hidden(X1,k1_relat_1(k2_funct_1(esk6_0)))|~v1_funct_1(k2_funct_1(esk6_0))|~v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_70, negated_conjecture, (k1_funct_1(esk6_0,k1_funct_1(k2_funct_1(esk6_0),esk5_0))!=esk5_0|~r2_hidden(esk5_0,k1_relat_1(k2_funct_1(esk6_0)))|~v1_funct_1(k2_funct_1(esk6_0))|~v1_relat_1(k2_funct_1(esk6_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.45  cnf(c_0_71, plain, (k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X2))=X2|~v2_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_32])).
% 0.20/0.45  cnf(c_0_72, negated_conjecture, (r2_hidden(esk5_0,k2_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_73, negated_conjecture, (~r2_hidden(esk5_0,k1_relat_1(k2_funct_1(esk6_0)))|~v1_funct_1(k2_funct_1(esk6_0))|~v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_36]), c_0_72]), c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_74, negated_conjecture, (~v1_funct_1(k2_funct_1(esk6_0))|~v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_35]), c_0_72]), c_0_36]), c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_75, negated_conjecture, (~v1_relat_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_18]), c_0_28]), c_0_29])])).
% 0.20/0.45  cnf(c_0_76, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_19]), c_0_28]), c_0_29])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 77
% 0.20/0.45  # Proof object clause steps            : 54
% 0.20/0.45  # Proof object formula steps           : 23
% 0.20/0.45  # Proof object conjectures             : 26
% 0.20/0.45  # Proof object clause conjectures      : 23
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 22
% 0.20/0.45  # Proof object initial formulas used   : 11
% 0.20/0.45  # Proof object generating inferences   : 29
% 0.20/0.45  # Proof object simplifying inferences  : 65
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 11
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 27
% 0.20/0.45  # Removed in clause preprocessing      : 0
% 0.20/0.45  # Initial clauses in saturation        : 27
% 0.20/0.45  # Processed clauses                    : 462
% 0.20/0.45  # ...of these trivial                  : 1
% 0.20/0.45  # ...subsumed                          : 159
% 0.20/0.45  # ...remaining for further processing  : 302
% 0.20/0.45  # Other redundant clauses eliminated   : 22
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 44
% 0.20/0.45  # Backward-rewritten                   : 49
% 0.20/0.45  # Generated clauses                    : 1955
% 0.20/0.45  # ...of the previous two non-trivial   : 1919
% 0.20/0.45  # Contextual simplify-reflections      : 42
% 0.20/0.45  # Paramodulations                      : 1928
% 0.20/0.45  # Factorizations                       : 6
% 0.20/0.45  # Equation resolutions                 : 22
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 175
% 0.20/0.45  #    Positive orientable unit clauses  : 8
% 0.20/0.45  #    Positive unorientable unit clauses: 0
% 0.20/0.45  #    Negative unit clauses             : 1
% 0.20/0.45  #    Non-unit-clauses                  : 166
% 0.20/0.45  # Current number of unprocessed clauses: 1508
% 0.20/0.45  # ...number of literals in the above   : 8825
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 120
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 17427
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 2834
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 245
% 0.20/0.45  # Unit Clause-clause subsumption calls : 35
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 1
% 0.20/0.45  # BW rewrite match successes           : 1
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 62366
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.099 s
% 0.20/0.45  # System time              : 0.007 s
% 0.20/0.45  # Total time               : 0.106 s
% 0.20/0.45  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
