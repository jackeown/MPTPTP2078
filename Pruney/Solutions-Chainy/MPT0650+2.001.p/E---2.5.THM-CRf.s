%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:45 EST 2020

% Result     : Theorem 1.20s
% Output     : CNFRefutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   92 (1360 expanded)
%              Number of clauses        :   65 ( 493 expanded)
%              Number of leaves         :   13 ( 337 expanded)
%              Depth                    :   31
%              Number of atoms          :  331 (5892 expanded)
%              Number of equality atoms :   61 (1573 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   19 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

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

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

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
    ! [X27] :
      ( ( k2_relat_1(X27) = k1_relat_1(k4_relat_1(X27))
        | ~ v1_relat_1(X27) )
      & ( k1_relat_1(X27) = k2_relat_1(k4_relat_1(X27))
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & v2_funct_1(esk5_0)
    & r2_hidden(esk4_0,k2_relat_1(esk5_0))
    & ( esk4_0 != k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))
      | esk4_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k1_relat_1(X1) = k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k4_relat_1(X2))
    | ~ r1_tarski(k4_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(X1))
    | ~ r1_tarski(X1,k4_relat_1(esk5_0))
    | ~ r1_tarski(k4_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_25,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v2_funct_1(X28)
      | k2_funct_1(X28) = k4_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_26,plain,(
    ! [X29] :
      ( ( v1_relat_1(k2_funct_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( v1_funct_1(k2_funct_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ r2_hidden(X30,k1_relat_1(X31))
      | r2_hidden(k1_funct_1(X31,X30),k2_relat_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(k4_relat_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_24])])).

cnf(c_0_29,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_21])])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_21])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k2_relat_1(k2_funct_1(esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_37,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_39,plain,(
    ! [X20] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k4_relat_1(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k2_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31]),c_0_21])])).

cnf(c_0_41,plain,
    ( k2_relat_1(k2_funct_1(X1)) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_29])).

cnf(c_0_42,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_30]),c_0_31]),c_0_21])])).

cnf(c_0_44,plain,
    ( r2_hidden(k1_funct_1(k4_relat_1(X1),X2),k2_relat_1(k4_relat_1(X1)))
    | ~ v1_funct_1(k4_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_17]),c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_43]),c_0_31]),c_0_21])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_funct_1(k4_relat_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),k2_relat_1(k4_relat_1(esk5_0)))
    | ~ v1_funct_1(k4_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_21])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),k2_relat_1(k2_funct_1(esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_29]),c_0_30]),c_0_31]),c_0_21])])).

fof(c_0_48,plain,(
    ! [X32,X33,X34] :
      ( ( r2_hidden(X32,k1_relat_1(X34))
        | ~ r2_hidden(X32,k1_relat_1(k5_relat_1(X34,X33)))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( r2_hidden(k1_funct_1(X34,X32),k1_relat_1(X33))
        | ~ r2_hidden(X32,k1_relat_1(k5_relat_1(X34,X33)))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) )
      & ( ~ r2_hidden(X32,k1_relat_1(X34))
        | ~ r2_hidden(k1_funct_1(X34,X32),k1_relat_1(X33))
        | r2_hidden(X32,k1_relat_1(k5_relat_1(X34,X33)))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),k2_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_37]),c_0_31]),c_0_21])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_41]),c_0_30]),c_0_31]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_31]),c_0_21]),c_0_35])])).

cnf(c_0_53,plain,
    ( k1_relat_1(k2_funct_1(X1)) = k2_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45]),c_0_30]),c_0_31]),c_0_21])])).

fof(c_0_55,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(X40,k1_relat_1(X42))
        | ~ r2_hidden(k4_tarski(X40,X41),X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( X41 = k1_funct_1(X42,X40)
        | ~ r2_hidden(k4_tarski(X40,X41),X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( ~ r2_hidden(X40,k1_relat_1(X42))
        | X41 != k1_funct_1(X42,X40)
        | r2_hidden(k4_tarski(X40,X41),X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_37]),c_0_31]),c_0_21])])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k2_funct_1(esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_31]),c_0_21]),c_0_35])])).

cnf(c_0_60,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_37]),c_0_31]),c_0_21])])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 != k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))
    | esk4_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)))),k2_funct_1(esk5_0))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_35])])).

fof(c_0_64,plain,(
    ! [X38,X39] :
      ( ( X38 = k1_funct_1(k2_funct_1(X39),k1_funct_1(X39,X38))
        | ~ v2_funct_1(X39)
        | ~ r2_hidden(X38,k1_relat_1(X39))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( X38 = k1_funct_1(k5_relat_1(X39,k2_funct_1(X39)),X38)
        | ~ v2_funct_1(X39)
        | ~ r2_hidden(X38,k1_relat_1(X39))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),esk4_0)) != esk4_0
    | k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),esk4_0) != esk4_0
    | ~ r1_tarski(X1,esk5_0)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_18])).

cnf(c_0_66,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)))),k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_37]),c_0_31]),c_0_21])])).

cnf(c_0_68,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),esk4_0) != esk4_0
    | k1_funct_1(X1,k1_funct_1(X2,X3)) != esk4_0
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k4_tarski(X3,k1_funct_1(k2_funct_1(X1),esk4_0)),X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,esk5_0)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_30]),c_0_31]),c_0_43]),c_0_21])])).

cnf(c_0_71,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)))) != esk4_0
    | k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) != esk4_0
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_35]),c_0_24])])).

fof(c_0_72,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ v1_funct_1(X36)
      | ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | ~ r2_hidden(X35,k1_relat_1(k5_relat_1(X37,X36)))
      | k1_funct_1(k5_relat_1(X37,X36),X35) = k1_funct_1(X36,k1_funct_1(X37,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_43]),c_0_31]),c_0_34]),c_0_21]),c_0_35])])).

cnf(c_0_74,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0) != esk4_0
    | k1_funct_1(esk5_0,X1) != esk4_0
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),X1),k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_66]),c_0_35])])).

cnf(c_0_75,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk4_0,k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_37]),c_0_31]),c_0_21])])).

cnf(c_0_77,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)) != esk4_0
    | k1_funct_1(esk5_0,X1) != esk4_0
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),X1),k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_31]),c_0_76]),c_0_35]),c_0_21])])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) != esk4_0
    | k1_funct_1(esk5_0,X2) != esk4_0
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk5_0,X1),X2),k2_funct_1(esk5_0))
    | ~ r2_hidden(k4_tarski(esk4_0,X1),k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_66]),c_0_35])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0))
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_34]),c_0_35])])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk5_0,X1) != esk4_0
    | k1_funct_1(esk5_0,X2) != esk4_0
    | ~ r2_hidden(k4_tarski(k1_funct_1(esk5_0,X1),X2),k2_funct_1(esk5_0))
    | ~ r2_hidden(k4_tarski(esk4_0,X1),k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_37]),c_0_31]),c_0_21])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_37]),c_0_31]),c_0_21])])).

fof(c_0_82,plain,(
    ! [X24,X25,X26] :
      ( ( r2_hidden(X24,k1_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26) )
      & ( r2_hidden(X25,k2_relat_1(X26))
        | ~ r2_hidden(k4_tarski(X24,X25),X26)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_83,negated_conjecture,
    ( k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_70]),c_0_81])])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_85,plain,(
    ! [X9,X10,X11,X13,X14,X15,X16,X18] :
      ( ( ~ r2_hidden(X11,X10)
        | r2_hidden(k4_tarski(esk1_3(X9,X10,X11),X11),X9)
        | X10 != k2_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X14,X13),X9)
        | r2_hidden(X13,X10)
        | X10 != k2_relat_1(X9) )
      & ( ~ r2_hidden(esk2_2(X15,X16),X16)
        | ~ r2_hidden(k4_tarski(X18,esk2_2(X15,X16)),X15)
        | X16 = k2_relat_1(X15) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r2_hidden(k4_tarski(esk3_2(X15,X16),esk2_2(X15,X16)),X15)
        | X16 = k2_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk5_0),esk4_0),esk4_0),esk5_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_66]),c_0_31]),c_0_21])])])).

cnf(c_0_87,plain,
    ( k1_funct_1(k2_funct_1(X1),X2) = X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(k4_tarski(X3,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_66]),c_0_84])).

cnf(c_0_88,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk4_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_30]),c_0_31]),c_0_21])])).

cnf(c_0_90,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.20/1.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 1.20/1.38  # and selection function PSelectUnlessUniqMaxPos.
% 1.20/1.38  #
% 1.20/1.38  # Preprocessing time       : 0.028 s
% 1.20/1.38  # Presaturation interreduction done
% 1.20/1.38  
% 1.20/1.38  # Proof found!
% 1.20/1.38  # SZS status Theorem
% 1.20/1.38  # SZS output start CNFRefutation
% 1.20/1.38  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 1.20/1.38  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 1.20/1.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.20/1.38  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 1.20/1.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.20/1.38  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 1.20/1.38  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.20/1.38  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 1.20/1.38  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 1.20/1.38  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 1.20/1.38  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 1.20/1.38  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 1.20/1.38  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 1.20/1.38  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 1.20/1.38  fof(c_0_14, plain, ![X27]:((k2_relat_1(X27)=k1_relat_1(k4_relat_1(X27))|~v1_relat_1(X27))&(k1_relat_1(X27)=k2_relat_1(k4_relat_1(X27))|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 1.20/1.38  fof(c_0_15, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.20/1.38  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&((v2_funct_1(esk5_0)&r2_hidden(esk4_0,k2_relat_1(esk5_0)))&(esk4_0!=k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))|esk4_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 1.20/1.38  cnf(c_0_17, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.20/1.38  cnf(c_0_18, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.20/1.38  cnf(c_0_19, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.20/1.38  cnf(c_0_20, plain, (k1_relat_1(X1)=k2_relat_1(X2)|~v1_relat_1(X2)|~r1_tarski(X1,k4_relat_1(X2))|~r1_tarski(k4_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 1.20/1.38  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.20/1.38  cnf(c_0_22, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.20/1.38  cnf(c_0_23, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(X1))|~r1_tarski(X1,k4_relat_1(esk5_0))|~r1_tarski(k4_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 1.20/1.38  cnf(c_0_24, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_22])).
% 1.20/1.38  fof(c_0_25, plain, ![X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v2_funct_1(X28)|k2_funct_1(X28)=k4_relat_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 1.20/1.38  fof(c_0_26, plain, ![X29]:((v1_relat_1(k2_funct_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(v1_funct_1(k2_funct_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.20/1.38  fof(c_0_27, plain, ![X30, X31]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~r2_hidden(X30,k1_relat_1(X31))|r2_hidden(k1_funct_1(X31,X30),k2_relat_1(X31)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 1.20/1.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(k4_relat_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_24])])).
% 1.20/1.38  cnf(c_0_29, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.20/1.38  cnf(c_0_30, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.20/1.38  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.20/1.38  cnf(c_0_32, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.20/1.38  cnf(c_0_33, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.20/1.38  cnf(c_0_34, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_36, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k2_relat_1(k2_funct_1(esk5_0)))|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 1.20/1.38  cnf(c_0_37, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.20/1.38  cnf(c_0_38, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.20/1.38  fof(c_0_39, plain, ![X20]:(~v1_relat_1(X20)|v1_relat_1(k4_relat_1(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 1.20/1.38  cnf(c_0_40, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k2_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_41, plain, (k2_relat_1(k2_funct_1(X1))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_29])).
% 1.20/1.38  cnf(c_0_42, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.20/1.38  cnf(c_0_43, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk5_0),esk4_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_30]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_44, plain, (r2_hidden(k1_funct_1(k4_relat_1(X1),X2),k2_relat_1(k4_relat_1(X1)))|~v1_funct_1(k4_relat_1(X1))|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_17]), c_0_42])).
% 1.20/1.38  cnf(c_0_45, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_43]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_funct_1(k4_relat_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),k2_relat_1(k4_relat_1(esk5_0)))|~v1_funct_1(k4_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_21])])).
% 1.20/1.38  cnf(c_0_47, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),k2_relat_1(k2_funct_1(esk5_0)))|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_29]), c_0_30]), c_0_31]), c_0_21])])).
% 1.20/1.38  fof(c_0_48, plain, ![X32, X33, X34]:(((r2_hidden(X32,k1_relat_1(X34))|~r2_hidden(X32,k1_relat_1(k5_relat_1(X34,X33)))|(~v1_relat_1(X34)|~v1_funct_1(X34))|(~v1_relat_1(X33)|~v1_funct_1(X33)))&(r2_hidden(k1_funct_1(X34,X32),k1_relat_1(X33))|~r2_hidden(X32,k1_relat_1(k5_relat_1(X34,X33)))|(~v1_relat_1(X34)|~v1_funct_1(X34))|(~v1_relat_1(X33)|~v1_funct_1(X33))))&(~r2_hidden(X32,k1_relat_1(X34))|~r2_hidden(k1_funct_1(X34,X32),k1_relat_1(X33))|r2_hidden(X32,k1_relat_1(k5_relat_1(X34,X33)))|(~v1_relat_1(X34)|~v1_funct_1(X34))|(~v1_relat_1(X33)|~v1_funct_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 1.20/1.38  cnf(c_0_49, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),k2_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_37]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_50, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.20/1.38  cnf(c_0_51, negated_conjecture, (r2_hidden(k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_41]), c_0_30]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_52, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)))|~v1_funct_1(k2_funct_1(esk5_0))|~r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_31]), c_0_21]), c_0_35])])).
% 1.20/1.38  cnf(c_0_53, plain, (k1_relat_1(k2_funct_1(X1))=k2_relat_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_29])).
% 1.20/1.38  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)))|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45]), c_0_30]), c_0_31]), c_0_21])])).
% 1.20/1.38  fof(c_0_55, plain, ![X40, X41, X42]:(((r2_hidden(X40,k1_relat_1(X42))|~r2_hidden(k4_tarski(X40,X41),X42)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(X41=k1_funct_1(X42,X40)|~r2_hidden(k4_tarski(X40,X41),X42)|(~v1_relat_1(X42)|~v1_funct_1(X42))))&(~r2_hidden(X40,k1_relat_1(X42))|X41!=k1_funct_1(X42,X40)|r2_hidden(k4_tarski(X40,X41),X42)|(~v1_relat_1(X42)|~v1_funct_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 1.20/1.38  cnf(c_0_56, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.20/1.38  cnf(c_0_57, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_37]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_58, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.20/1.38  cnf(c_0_59, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k2_funct_1(esk5_0)))|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_31]), c_0_21]), c_0_35])])).
% 1.20/1.38  cnf(c_0_60, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)), inference(er,[status(thm)],[c_0_58])).
% 1.20/1.38  cnf(c_0_61, negated_conjecture, (r2_hidden(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_37]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_62, negated_conjecture, (esk4_0!=k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))|esk4_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.20/1.38  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)))),k2_funct_1(esk5_0))|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_35])])).
% 1.20/1.38  fof(c_0_64, plain, ![X38, X39]:((X38=k1_funct_1(k2_funct_1(X39),k1_funct_1(X39,X38))|(~v2_funct_1(X39)|~r2_hidden(X38,k1_relat_1(X39)))|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(X38=k1_funct_1(k5_relat_1(X39,k2_funct_1(X39)),X38)|(~v2_funct_1(X39)|~r2_hidden(X38,k1_relat_1(X39)))|(~v1_relat_1(X39)|~v1_funct_1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 1.20/1.38  cnf(c_0_65, negated_conjecture, (k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),esk4_0))!=esk4_0|k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),esk4_0)!=esk4_0|~r1_tarski(X1,esk5_0)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_18])).
% 1.20/1.38  cnf(c_0_66, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.20/1.38  cnf(c_0_67, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)))),k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_37]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_68, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 1.20/1.38  cnf(c_0_69, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),esk4_0)!=esk4_0|k1_funct_1(X1,k1_funct_1(X2,X3))!=esk4_0|~v1_funct_1(X2)|~r2_hidden(k4_tarski(X3,k1_funct_1(k2_funct_1(X1),esk4_0)),X2)|~v1_relat_1(X2)|~r1_tarski(X1,esk5_0)|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.20/1.38  cnf(c_0_70, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_30]), c_0_31]), c_0_43]), c_0_21])])).
% 1.20/1.38  cnf(c_0_71, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))))!=esk4_0|k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)!=esk4_0|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_35]), c_0_24])])).
% 1.20/1.38  fof(c_0_72, plain, ![X35, X36, X37]:(~v1_relat_1(X36)|~v1_funct_1(X36)|(~v1_relat_1(X37)|~v1_funct_1(X37)|(~r2_hidden(X35,k1_relat_1(k5_relat_1(X37,X36)))|k1_funct_1(k5_relat_1(X37,X36),X35)=k1_funct_1(X36,k1_funct_1(X37,X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 1.20/1.38  cnf(c_0_73, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)))|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_43]), c_0_31]), c_0_34]), c_0_21]), c_0_35])])).
% 1.20/1.38  cnf(c_0_74, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0),esk4_0)!=esk4_0|k1_funct_1(esk5_0,X1)!=esk4_0|~v1_funct_1(k2_funct_1(esk5_0))|~r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),X1),k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_66]), c_0_35])])).
% 1.20/1.38  cnf(c_0_75, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 1.20/1.38  cnf(c_0_76, negated_conjecture, (r2_hidden(esk4_0,k1_relat_1(k5_relat_1(k2_funct_1(esk5_0),esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_37]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_77, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))!=esk4_0|k1_funct_1(esk5_0,X1)!=esk4_0|~v1_funct_1(k2_funct_1(esk5_0))|~r2_hidden(k4_tarski(k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),X1),k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_31]), c_0_76]), c_0_35]), c_0_21])])).
% 1.20/1.38  cnf(c_0_78, negated_conjecture, (k1_funct_1(esk5_0,X1)!=esk4_0|k1_funct_1(esk5_0,X2)!=esk4_0|~v1_funct_1(k2_funct_1(esk5_0))|~r2_hidden(k4_tarski(k1_funct_1(esk5_0,X1),X2),k2_funct_1(esk5_0))|~r2_hidden(k4_tarski(esk4_0,X1),k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_66]), c_0_35])])).
% 1.20/1.38  cnf(c_0_79, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0))|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_34]), c_0_35])])).
% 1.20/1.38  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk5_0,X1)!=esk4_0|k1_funct_1(esk5_0,X2)!=esk4_0|~r2_hidden(k4_tarski(k1_funct_1(esk5_0,X1),X2),k2_funct_1(esk5_0))|~r2_hidden(k4_tarski(esk4_0,X1),k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_37]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_81, negated_conjecture, (r2_hidden(k4_tarski(esk4_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0)),k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_37]), c_0_31]), c_0_21])])).
% 1.20/1.38  fof(c_0_82, plain, ![X24, X25, X26]:((r2_hidden(X24,k1_relat_1(X26))|~r2_hidden(k4_tarski(X24,X25),X26)|~v1_relat_1(X26))&(r2_hidden(X25,k2_relat_1(X26))|~r2_hidden(k4_tarski(X24,X25),X26)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 1.20/1.38  cnf(c_0_83, negated_conjecture, (k1_funct_1(esk5_0,k1_funct_1(k2_funct_1(esk5_0),esk4_0))!=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_70]), c_0_81])])).
% 1.20/1.38  cnf(c_0_84, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.20/1.38  fof(c_0_85, plain, ![X9, X10, X11, X13, X14, X15, X16, X18]:(((~r2_hidden(X11,X10)|r2_hidden(k4_tarski(esk1_3(X9,X10,X11),X11),X9)|X10!=k2_relat_1(X9))&(~r2_hidden(k4_tarski(X14,X13),X9)|r2_hidden(X13,X10)|X10!=k2_relat_1(X9)))&((~r2_hidden(esk2_2(X15,X16),X16)|~r2_hidden(k4_tarski(X18,esk2_2(X15,X16)),X15)|X16=k2_relat_1(X15))&(r2_hidden(esk2_2(X15,X16),X16)|r2_hidden(k4_tarski(esk3_2(X15,X16),esk2_2(X15,X16)),X15)|X16=k2_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.20/1.38  cnf(c_0_86, negated_conjecture, (~r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk5_0),esk4_0),esk4_0),esk5_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_66]), c_0_31]), c_0_21])])])).
% 1.20/1.38  cnf(c_0_87, plain, (k1_funct_1(k2_funct_1(X1),X2)=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~r2_hidden(k4_tarski(X3,X2),X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_66]), c_0_84])).
% 1.20/1.38  cnf(c_0_88, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.20/1.38  cnf(c_0_89, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk4_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_30]), c_0_31]), c_0_21])])).
% 1.20/1.38  cnf(c_0_90, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_88])).
% 1.20/1.38  cnf(c_0_91, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_19])]), ['proof']).
% 1.20/1.38  # SZS output end CNFRefutation
% 1.20/1.38  # Proof object total steps             : 92
% 1.20/1.38  # Proof object clause steps            : 65
% 1.20/1.38  # Proof object formula steps           : 27
% 1.20/1.38  # Proof object conjectures             : 43
% 1.20/1.38  # Proof object clause conjectures      : 40
% 1.20/1.38  # Proof object formula conjectures     : 3
% 1.20/1.38  # Proof object initial clauses used    : 22
% 1.20/1.38  # Proof object initial formulas used   : 13
% 1.20/1.38  # Proof object generating inferences   : 40
% 1.20/1.38  # Proof object simplifying inferences  : 109
% 1.20/1.38  # Training examples: 0 positive, 0 negative
% 1.20/1.38  # Parsed axioms                        : 15
% 1.20/1.38  # Removed by relevancy pruning/SinE    : 0
% 1.20/1.38  # Initial clauses                      : 33
% 1.20/1.38  # Removed in clause preprocessing      : 0
% 1.20/1.38  # Initial clauses in saturation        : 33
% 1.20/1.38  # Processed clauses                    : 2329
% 1.20/1.38  # ...of these trivial                  : 0
% 1.20/1.38  # ...subsumed                          : 1135
% 1.20/1.38  # ...remaining for further processing  : 1194
% 1.20/1.38  # Other redundant clauses eliminated   : 2485
% 1.20/1.38  # Clauses deleted for lack of memory   : 0
% 1.20/1.38  # Backward-subsumed                    : 330
% 1.20/1.38  # Backward-rewritten                   : 24
% 1.20/1.38  # Generated clauses                    : 88204
% 1.20/1.38  # ...of the previous two non-trivial   : 85425
% 1.20/1.38  # Contextual simplify-reflections      : 46
% 1.20/1.38  # Paramodulations                      : 85719
% 1.20/1.38  # Factorizations                       : 0
% 1.20/1.38  # Equation resolutions                 : 2485
% 1.20/1.38  # Propositional unsat checks           : 0
% 1.20/1.38  #    Propositional check models        : 0
% 1.20/1.38  #    Propositional check unsatisfiable : 0
% 1.20/1.38  #    Propositional clauses             : 0
% 1.20/1.38  #    Propositional clauses after purity: 0
% 1.20/1.38  #    Propositional unsat core size     : 0
% 1.20/1.38  #    Propositional preprocessing time  : 0.000
% 1.20/1.38  #    Propositional encoding time       : 0.000
% 1.20/1.38  #    Propositional solver time         : 0.000
% 1.20/1.38  #    Success case prop preproc time    : 0.000
% 1.20/1.38  #    Success case prop encoding time   : 0.000
% 1.20/1.38  #    Success case prop solver time     : 0.000
% 1.20/1.38  # Current number of processed clauses  : 805
% 1.20/1.38  #    Positive orientable unit clauses  : 60
% 1.20/1.38  #    Positive unorientable unit clauses: 0
% 1.20/1.38  #    Negative unit clauses             : 9
% 1.20/1.38  #    Non-unit-clauses                  : 736
% 1.20/1.38  # Current number of unprocessed clauses: 83068
% 1.20/1.38  # ...number of literals in the above   : 592501
% 1.20/1.38  # Current number of archived formulas  : 0
% 1.20/1.38  # Current number of archived clauses   : 384
% 1.20/1.38  # Clause-clause subsumption calls (NU) : 91468
% 1.20/1.38  # Rec. Clause-clause subsumption calls : 28831
% 1.20/1.38  # Non-unit clause-clause subsumptions  : 1406
% 1.20/1.38  # Unit Clause-clause subsumption calls : 1263
% 1.20/1.38  # Rewrite failures with RHS unbound    : 0
% 1.20/1.38  # BW rewrite match attempts            : 275
% 1.20/1.38  # BW rewrite match successes           : 20
% 1.20/1.38  # Condensation attempts                : 0
% 1.20/1.38  # Condensation successes               : 0
% 1.20/1.38  # Termbank termtop insertions          : 2185857
% 1.20/1.38  
% 1.20/1.38  # -------------------------------------------------
% 1.20/1.38  # User time                : 0.977 s
% 1.20/1.38  # System time              : 0.053 s
% 1.20/1.38  # Total time               : 1.029 s
% 1.20/1.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
