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
% DateTime   : Thu Dec  3 10:53:47 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 353 expanded)
%              Number of clauses        :   42 ( 130 expanded)
%              Number of leaves         :   13 (  88 expanded)
%              Depth                    :   10
%              Number of atoms          :  289 (1575 expanded)
%              Number of equality atoms :   58 ( 411 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

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

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t40_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(k1_funct_1(X3,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

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
    ! [X36,X37,X38] :
      ( ( k1_relat_1(X37) = X36
        | X37 != k6_relat_1(X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( ~ r2_hidden(X38,X36)
        | k1_funct_1(X37,X38) = X38
        | X37 != k6_relat_1(X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( r2_hidden(esk6_2(X36,X37),X36)
        | k1_relat_1(X37) != X36
        | X37 = k6_relat_1(X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( k1_funct_1(X37,esk6_2(X36,X37)) != esk6_2(X36,X37)
        | k1_relat_1(X37) != X36
        | X37 = k6_relat_1(X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_15,plain,(
    ! [X32] :
      ( v1_relat_1(k6_relat_1(X32))
      & v1_funct_1(k6_relat_1(X32)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_16,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ v2_funct_1(X30)
      | k2_funct_1(X30) = k4_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_17,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & v2_funct_1(esk8_0)
    & r2_hidden(esk7_0,k2_relat_1(esk8_0))
    & ( esk7_0 != k1_funct_1(esk8_0,k1_funct_1(k2_funct_1(esk8_0),esk7_0))
      | esk7_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk8_0),esk8_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_18,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ v1_relat_1(X26)
      | k1_relat_1(k5_relat_1(X25,X26)) = k10_relat_1(X25,k1_relat_1(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_19,plain,
    ( k1_relat_1(X1) = X2
    | X1 != k6_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X16,X17,X18,X19,X20,X21] :
      ( ( ~ r2_hidden(k4_tarski(X18,X19),X17)
        | r2_hidden(k4_tarski(X19,X18),X16)
        | X17 != k4_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X21,X20),X16)
        | r2_hidden(k4_tarski(X20,X21),X17)
        | X17 != k4_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X16,X17),esk5_2(X16,X17)),X17)
        | ~ r2_hidden(k4_tarski(esk5_2(X16,X17),esk4_2(X16,X17)),X16)
        | X17 = k4_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk4_2(X16,X17),esk5_2(X16,X17)),X17)
        | r2_hidden(k4_tarski(esk5_2(X16,X17),esk4_2(X16,X17)),X16)
        | X17 = k4_relat_1(X16)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_23,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k4_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_24,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v2_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X31] :
      ( ( v1_relat_1(k2_funct_1(X31))
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( v1_funct_1(k2_funct_1(X31))
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_29,plain,(
    ! [X40,X41,X42] :
      ( ( r2_hidden(X40,k1_relat_1(X42))
        | ~ r2_hidden(X40,k1_relat_1(k5_relat_1(X42,k6_relat_1(X41))))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( r2_hidden(k1_funct_1(X42,X40),X41)
        | ~ r2_hidden(X40,k1_relat_1(k5_relat_1(X42,k6_relat_1(X41))))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( ~ r2_hidden(X40,k1_relat_1(X42))
        | ~ r2_hidden(k1_funct_1(X42,X40),X41)
        | r2_hidden(X40,k1_relat_1(k5_relat_1(X42,k6_relat_1(X41))))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).

cnf(c_0_30,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20]),c_0_21])])).

fof(c_0_32,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( ~ r2_hidden(X7,X6)
        | r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)
        | X6 != k2_relat_1(X5) )
      & ( ~ r2_hidden(k4_tarski(X10,X9),X5)
        | r2_hidden(X9,X6)
        | X6 != k2_relat_1(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)
        | X12 = k2_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)
        | X12 = k2_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_33,plain,(
    ! [X43,X44,X45] :
      ( ( r2_hidden(X43,k1_relat_1(X45))
        | ~ r2_hidden(k4_tarski(X43,X44),X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( X44 = k1_funct_1(X45,X43)
        | ~ r2_hidden(k4_tarski(X43,X44),X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( ~ r2_hidden(X43,k1_relat_1(X45))
        | X44 != k1_funct_1(X45,X43)
        | r2_hidden(k4_tarski(X43,X44),X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( esk7_0 != k1_funct_1(esk8_0,k1_funct_1(k2_funct_1(esk8_0),esk7_0))
    | esk7_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk8_0),esk8_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( k2_funct_1(esk8_0) = k4_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

fof(c_0_38,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | ~ r2_hidden(X33,k1_relat_1(k5_relat_1(X35,X34)))
      | k1_funct_1(k5_relat_1(X35,X34),X33) = k1_funct_1(X34,k1_funct_1(X35,X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).

cnf(c_0_39,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( k1_relat_1(k5_relat_1(X1,k6_relat_1(X2))) = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_21])])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(k4_relat_1(esk8_0),esk7_0)) != esk7_0
    | k1_funct_1(k5_relat_1(k4_relat_1(esk8_0),esk8_0),esk7_0) != esk7_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37]),c_0_37])).

cnf(c_0_47,plain,
    ( k1_funct_1(k5_relat_1(X2,X1),X3) = k1_funct_1(X1,k1_funct_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_26]),c_0_27])])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_37]),c_0_26]),c_0_27])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k1_funct_1(X2,X1),X3)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( X1 = k1_funct_1(k4_relat_1(X2),X3)
    | ~ v1_funct_1(k4_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_35])).

fof(c_0_53,plain,(
    ! [X27,X28,X29] :
      ( ( r2_hidden(X27,k1_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(X28,k2_relat_1(X29))
        | ~ r2_hidden(k4_tarski(X27,X28),X29)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_54,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(k4_relat_1(esk8_0),esk7_0)) != esk7_0
    | ~ r2_hidden(esk7_0,k1_relat_1(k5_relat_1(k4_relat_1(esk8_0),esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_26]),c_0_49]),c_0_27])])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_30])).

cnf(c_0_56,plain,
    ( k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_51])).

cnf(c_0_57,plain,
    ( esk1_3(X1,k2_relat_1(X1),X2) = k1_funct_1(k4_relat_1(X1),X2)
    | ~ v1_funct_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_58,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk8_0,k1_funct_1(k4_relat_1(esk8_0),esk7_0)) != esk7_0
    | ~ r2_hidden(k1_funct_1(k4_relat_1(esk8_0),esk7_0),k1_relat_1(esk8_0))
    | ~ r2_hidden(esk7_0,k1_relat_1(k4_relat_1(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_48]),c_0_49]),c_0_27])])).

cnf(c_0_60,plain,
    ( k1_funct_1(X1,k1_funct_1(k4_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(k4_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk7_0,k2_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_62,plain,
    ( r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(k4_relat_1(esk8_0),esk7_0),k1_relat_1(esk8_0))
    | ~ r2_hidden(esk7_0,k1_relat_1(k4_relat_1(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_48]),c_0_26]),c_0_27]),c_0_61])])).

cnf(c_0_64,plain,
    ( r2_hidden(k1_funct_1(k4_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_57])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k1_relat_1(k4_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_35])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k1_relat_1(k4_relat_1(esk8_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_48]),c_0_27]),c_0_61])])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k1_relat_1(k4_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_51])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_27]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.38/1.54  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.38/1.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.38/1.54  #
% 1.38/1.54  # Preprocessing time       : 0.029 s
% 1.38/1.54  # Presaturation interreduction done
% 1.38/1.54  
% 1.38/1.54  # Proof found!
% 1.38/1.54  # SZS status Theorem
% 1.38/1.54  # SZS output start CNFRefutation
% 1.38/1.54  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 1.38/1.54  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 1.38/1.54  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.38/1.54  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 1.38/1.54  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 1.38/1.54  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 1.38/1.54  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 1.38/1.54  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.38/1.54  fof(t40_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,k6_relat_1(X2))))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_1)).
% 1.38/1.54  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 1.38/1.54  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 1.38/1.54  fof(t22_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))=>k1_funct_1(k5_relat_1(X3,X2),X1)=k1_funct_1(X2,k1_funct_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_funct_1)).
% 1.38/1.54  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 1.38/1.54  fof(c_0_13, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 1.38/1.54  fof(c_0_14, plain, ![X36, X37, X38]:(((k1_relat_1(X37)=X36|X37!=k6_relat_1(X36)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(~r2_hidden(X38,X36)|k1_funct_1(X37,X38)=X38|X37!=k6_relat_1(X36)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&((r2_hidden(esk6_2(X36,X37),X36)|k1_relat_1(X37)!=X36|X37=k6_relat_1(X36)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(k1_funct_1(X37,esk6_2(X36,X37))!=esk6_2(X36,X37)|k1_relat_1(X37)!=X36|X37=k6_relat_1(X36)|(~v1_relat_1(X37)|~v1_funct_1(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 1.38/1.54  fof(c_0_15, plain, ![X32]:(v1_relat_1(k6_relat_1(X32))&v1_funct_1(k6_relat_1(X32))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 1.38/1.54  fof(c_0_16, plain, ![X30]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~v2_funct_1(X30)|k2_funct_1(X30)=k4_relat_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 1.38/1.54  fof(c_0_17, negated_conjecture, ((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&((v2_funct_1(esk8_0)&r2_hidden(esk7_0,k2_relat_1(esk8_0)))&(esk7_0!=k1_funct_1(esk8_0,k1_funct_1(k2_funct_1(esk8_0),esk7_0))|esk7_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk8_0),esk8_0),esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 1.38/1.54  fof(c_0_18, plain, ![X25, X26]:(~v1_relat_1(X25)|(~v1_relat_1(X26)|k1_relat_1(k5_relat_1(X25,X26))=k10_relat_1(X25,k1_relat_1(X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 1.38/1.54  cnf(c_0_19, plain, (k1_relat_1(X1)=X2|X1!=k6_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.38/1.54  cnf(c_0_20, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.38/1.54  cnf(c_0_21, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.38/1.54  fof(c_0_22, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(k4_tarski(X18,X19),X17)|r2_hidden(k4_tarski(X19,X18),X16)|X17!=k4_relat_1(X16)|~v1_relat_1(X17)|~v1_relat_1(X16))&(~r2_hidden(k4_tarski(X21,X20),X16)|r2_hidden(k4_tarski(X20,X21),X17)|X17!=k4_relat_1(X16)|~v1_relat_1(X17)|~v1_relat_1(X16)))&((~r2_hidden(k4_tarski(esk4_2(X16,X17),esk5_2(X16,X17)),X17)|~r2_hidden(k4_tarski(esk5_2(X16,X17),esk4_2(X16,X17)),X16)|X17=k4_relat_1(X16)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk4_2(X16,X17),esk5_2(X16,X17)),X17)|r2_hidden(k4_tarski(esk5_2(X16,X17),esk4_2(X16,X17)),X16)|X17=k4_relat_1(X16)|~v1_relat_1(X17)|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 1.38/1.54  fof(c_0_23, plain, ![X24]:(~v1_relat_1(X24)|v1_relat_1(k4_relat_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 1.38/1.54  cnf(c_0_24, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.38/1.54  cnf(c_0_25, negated_conjecture, (v2_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.38/1.54  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.38/1.54  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.38/1.54  fof(c_0_28, plain, ![X31]:((v1_relat_1(k2_funct_1(X31))|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(v1_funct_1(k2_funct_1(X31))|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.38/1.54  fof(c_0_29, plain, ![X40, X41, X42]:(((r2_hidden(X40,k1_relat_1(X42))|~r2_hidden(X40,k1_relat_1(k5_relat_1(X42,k6_relat_1(X41))))|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(r2_hidden(k1_funct_1(X42,X40),X41)|~r2_hidden(X40,k1_relat_1(k5_relat_1(X42,k6_relat_1(X41))))|(~v1_relat_1(X42)|~v1_funct_1(X42))))&(~r2_hidden(X40,k1_relat_1(X42))|~r2_hidden(k1_funct_1(X42,X40),X41)|r2_hidden(X40,k1_relat_1(k5_relat_1(X42,k6_relat_1(X41))))|(~v1_relat_1(X42)|~v1_funct_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_funct_1])])])).
% 1.38/1.54  cnf(c_0_30, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.38/1.54  cnf(c_0_31, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20]), c_0_21])])).
% 1.38/1.54  fof(c_0_32, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)|X6!=k2_relat_1(X5))&(~r2_hidden(k4_tarski(X10,X9),X5)|r2_hidden(X9,X6)|X6!=k2_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.38/1.54  fof(c_0_33, plain, ![X43, X44, X45]:(((r2_hidden(X43,k1_relat_1(X45))|~r2_hidden(k4_tarski(X43,X44),X45)|(~v1_relat_1(X45)|~v1_funct_1(X45)))&(X44=k1_funct_1(X45,X43)|~r2_hidden(k4_tarski(X43,X44),X45)|(~v1_relat_1(X45)|~v1_funct_1(X45))))&(~r2_hidden(X43,k1_relat_1(X45))|X44!=k1_funct_1(X45,X43)|r2_hidden(k4_tarski(X43,X44),X45)|(~v1_relat_1(X45)|~v1_funct_1(X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 1.38/1.54  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k4_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.38/1.54  cnf(c_0_35, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.38/1.54  cnf(c_0_36, negated_conjecture, (esk7_0!=k1_funct_1(esk8_0,k1_funct_1(k2_funct_1(esk8_0),esk7_0))|esk7_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk8_0),esk8_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.38/1.54  cnf(c_0_37, negated_conjecture, (k2_funct_1(esk8_0)=k4_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])).
% 1.38/1.54  fof(c_0_38, plain, ![X33, X34, X35]:(~v1_relat_1(X34)|~v1_funct_1(X34)|(~v1_relat_1(X35)|~v1_funct_1(X35)|(~r2_hidden(X33,k1_relat_1(k5_relat_1(X35,X34)))|k1_funct_1(k5_relat_1(X35,X34),X33)=k1_funct_1(X34,k1_funct_1(X35,X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_funct_1])])])).
% 1.38/1.54  cnf(c_0_39, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.38/1.54  cnf(c_0_40, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.38/1.54  cnf(c_0_41, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,k6_relat_1(X3))))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.38/1.54  cnf(c_0_42, plain, (k1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))=k10_relat_1(X1,X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_21])])).
% 1.38/1.54  cnf(c_0_43, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.38/1.54  cnf(c_0_44, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.38/1.54  cnf(c_0_45, plain, (r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X2,X1),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_35])).
% 1.38/1.54  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk8_0,k1_funct_1(k4_relat_1(esk8_0),esk7_0))!=esk7_0|k1_funct_1(k5_relat_1(k4_relat_1(esk8_0),esk8_0),esk7_0)!=esk7_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37]), c_0_37])).
% 1.38/1.54  cnf(c_0_47, plain, (k1_funct_1(k5_relat_1(X2,X1),X3)=k1_funct_1(X1,k1_funct_1(X2,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(k5_relat_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.38/1.54  cnf(c_0_48, negated_conjecture, (v1_funct_1(k4_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_37]), c_0_26]), c_0_27])])).
% 1.38/1.54  cnf(c_0_49, negated_conjecture, (v1_relat_1(k4_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_37]), c_0_26]), c_0_27])])).
% 1.38/1.54  cnf(c_0_50, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(k1_funct_1(X2,X1),X3)|~r2_hidden(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.38/1.54  cnf(c_0_51, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_43])).
% 1.38/1.54  cnf(c_0_52, plain, (X1=k1_funct_1(k4_relat_1(X2),X3)|~v1_funct_1(k4_relat_1(X2))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X3),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_35])).
% 1.38/1.54  fof(c_0_53, plain, ![X27, X28, X29]:((r2_hidden(X27,k1_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|~v1_relat_1(X29))&(r2_hidden(X28,k2_relat_1(X29))|~r2_hidden(k4_tarski(X27,X28),X29)|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 1.38/1.54  cnf(c_0_54, negated_conjecture, (k1_funct_1(esk8_0,k1_funct_1(k4_relat_1(esk8_0),esk7_0))!=esk7_0|~r2_hidden(esk7_0,k1_relat_1(k5_relat_1(k4_relat_1(esk8_0),esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_26]), c_0_49]), c_0_27])])).
% 1.38/1.54  cnf(c_0_55, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_funct_1(X2)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))|~r2_hidden(X1,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_50, c_0_30])).
% 1.38/1.54  cnf(c_0_56, plain, (k1_funct_1(X1,esk1_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_44, c_0_51])).
% 1.38/1.54  cnf(c_0_57, plain, (esk1_3(X1,k2_relat_1(X1),X2)=k1_funct_1(k4_relat_1(X1),X2)|~v1_funct_1(k4_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 1.38/1.54  cnf(c_0_58, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.38/1.54  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk8_0,k1_funct_1(k4_relat_1(esk8_0),esk7_0))!=esk7_0|~r2_hidden(k1_funct_1(k4_relat_1(esk8_0),esk7_0),k1_relat_1(esk8_0))|~r2_hidden(esk7_0,k1_relat_1(k4_relat_1(esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_48]), c_0_49]), c_0_27])])).
% 1.38/1.54  cnf(c_0_60, plain, (k1_funct_1(X1,k1_funct_1(k4_relat_1(X1),X2))=X2|~v1_funct_1(k4_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.38/1.54  cnf(c_0_61, negated_conjecture, (r2_hidden(esk7_0,k2_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.38/1.54  cnf(c_0_62, plain, (r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_58, c_0_51])).
% 1.38/1.54  cnf(c_0_63, negated_conjecture, (~r2_hidden(k1_funct_1(k4_relat_1(esk8_0),esk7_0),k1_relat_1(esk8_0))|~r2_hidden(esk7_0,k1_relat_1(k4_relat_1(esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_48]), c_0_26]), c_0_27]), c_0_61])])).
% 1.38/1.54  cnf(c_0_64, plain, (r2_hidden(k1_funct_1(k4_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(k4_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_62, c_0_57])).
% 1.38/1.54  cnf(c_0_65, plain, (r2_hidden(X1,k1_relat_1(k4_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X3,X1),X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_45]), c_0_35])).
% 1.38/1.54  cnf(c_0_66, negated_conjecture, (~r2_hidden(esk7_0,k1_relat_1(k4_relat_1(esk8_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_48]), c_0_27]), c_0_61])])).
% 1.38/1.54  cnf(c_0_67, plain, (r2_hidden(X1,k1_relat_1(k4_relat_1(X2)))|~v1_relat_1(X2)|~r2_hidden(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_65, c_0_51])).
% 1.38/1.54  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_27]), c_0_61])]), ['proof']).
% 1.38/1.54  # SZS output end CNFRefutation
% 1.38/1.54  # Proof object total steps             : 69
% 1.38/1.54  # Proof object clause steps            : 42
% 1.38/1.54  # Proof object formula steps           : 27
% 1.38/1.54  # Proof object conjectures             : 17
% 1.38/1.54  # Proof object clause conjectures      : 14
% 1.38/1.54  # Proof object formula conjectures     : 3
% 1.38/1.54  # Proof object initial clauses used    : 19
% 1.38/1.54  # Proof object initial formulas used   : 13
% 1.38/1.54  # Proof object generating inferences   : 19
% 1.38/1.54  # Proof object simplifying inferences  : 43
% 1.38/1.54  # Training examples: 0 positive, 0 negative
% 1.38/1.54  # Parsed axioms                        : 13
% 1.38/1.54  # Removed by relevancy pruning/SinE    : 0
% 1.38/1.54  # Initial clauses                      : 33
% 1.38/1.54  # Removed in clause preprocessing      : 0
% 1.38/1.54  # Initial clauses in saturation        : 33
% 1.38/1.54  # Processed clauses                    : 2125
% 1.38/1.54  # ...of these trivial                  : 0
% 1.38/1.54  # ...subsumed                          : 803
% 1.38/1.54  # ...remaining for further processing  : 1322
% 1.38/1.54  # Other redundant clauses eliminated   : 9
% 1.38/1.54  # Clauses deleted for lack of memory   : 0
% 1.38/1.54  # Backward-subsumed                    : 5
% 1.38/1.54  # Backward-rewritten                   : 1
% 1.38/1.54  # Generated clauses                    : 106892
% 1.38/1.54  # ...of the previous two non-trivial   : 106842
% 1.38/1.54  # Contextual simplify-reflections      : 34
% 1.38/1.54  # Paramodulations                      : 106865
% 1.38/1.54  # Factorizations                       : 18
% 1.38/1.54  # Equation resolutions                 : 9
% 1.38/1.54  # Propositional unsat checks           : 0
% 1.38/1.54  #    Propositional check models        : 0
% 1.38/1.54  #    Propositional check unsatisfiable : 0
% 1.38/1.54  #    Propositional clauses             : 0
% 1.38/1.54  #    Propositional clauses after purity: 0
% 1.38/1.54  #    Propositional unsat core size     : 0
% 1.38/1.54  #    Propositional preprocessing time  : 0.000
% 1.38/1.54  #    Propositional encoding time       : 0.000
% 1.38/1.54  #    Propositional solver time         : 0.000
% 1.38/1.54  #    Success case prop preproc time    : 0.000
% 1.38/1.54  #    Success case prop encoding time   : 0.000
% 1.38/1.54  #    Success case prop solver time     : 0.000
% 1.38/1.54  # Current number of processed clauses  : 1276
% 1.38/1.54  #    Positive orientable unit clauses  : 10
% 1.38/1.54  #    Positive unorientable unit clauses: 0
% 1.38/1.54  #    Negative unit clauses             : 1
% 1.38/1.54  #    Non-unit-clauses                  : 1265
% 1.38/1.54  # Current number of unprocessed clauses: 104779
% 1.38/1.54  # ...number of literals in the above   : 306726
% 1.38/1.54  # Current number of archived formulas  : 0
% 1.38/1.54  # Current number of archived clauses   : 37
% 1.38/1.54  # Clause-clause subsumption calls (NU) : 260367
% 1.38/1.54  # Rec. Clause-clause subsumption calls : 202084
% 1.38/1.54  # Non-unit clause-clause subsumptions  : 842
% 1.38/1.54  # Unit Clause-clause subsumption calls : 230
% 1.38/1.54  # Rewrite failures with RHS unbound    : 0
% 1.38/1.54  # BW rewrite match attempts            : 1
% 1.38/1.54  # BW rewrite match successes           : 1
% 1.38/1.54  # Condensation attempts                : 0
% 1.38/1.54  # Condensation successes               : 0
% 1.38/1.54  # Termbank termtop insertions          : 3188876
% 1.38/1.55  
% 1.38/1.55  # -------------------------------------------------
% 1.38/1.55  # User time                : 1.128 s
% 1.38/1.55  # System time              : 0.071 s
% 1.38/1.55  # Total time               : 1.199 s
% 1.38/1.55  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
