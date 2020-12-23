%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:47 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 614 expanded)
%              Number of clauses        :   38 ( 228 expanded)
%              Number of leaves         :    9 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 (2853 expanded)
%              Number of equality atoms :   35 ( 696 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t20_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k2_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(t57_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k2_relat_1(X2)) )
       => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
          & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

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

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(t23_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(X2))
           => k1_funct_1(k5_relat_1(X2,X3),X1) = k1_funct_1(X3,k1_funct_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(X26,k2_relat_1(X27))
        | ~ r2_hidden(k4_tarski(X25,X26),X27)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( v2_funct_1(X2)
            & r2_hidden(X1,k2_relat_1(X2)) )
         => ( X1 = k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))
            & X1 = k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_funct_1])).

fof(c_0_13,plain,(
    ! [X33,X34,X35] :
      ( ( r2_hidden(X33,k1_relat_1(X35))
        | ~ r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( X34 = k1_funct_1(X35,X33)
        | ~ r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X33,k1_relat_1(X35))
        | X34 != k1_funct_1(X35,X33)
        | r2_hidden(k4_tarski(X33,X34),X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_11])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v2_funct_1(esk7_0)
    & r2_hidden(esk6_0,k2_relat_1(esk7_0))
    & ( esk6_0 != k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))
      | esk6_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_17,plain,(
    ! [X29] :
      ( ( v1_relat_1(k2_funct_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( v1_funct_1(k2_funct_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_18,plain,(
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

fof(c_0_19,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | v1_relat_1(k4_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v2_funct_1(X28)
      | k2_funct_1(X28) = k4_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_25,negated_conjecture,
    ( esk6_0 != k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))
    | esk6_0 != k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X31)
      | ~ v1_funct_1(X31)
      | ~ v1_relat_1(X32)
      | ~ v1_funct_1(X32)
      | ~ r2_hidden(X30,k1_relat_1(X31))
      | k1_funct_1(k5_relat_1(X31,X32),X30) = k1_funct_1(X32,k1_funct_1(X31,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).

cnf(c_0_28,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0),k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_34,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0) != esk6_0
    | k1_funct_1(X1,X2) != esk6_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,plain,
    ( k1_funct_1(k5_relat_1(X1,X2),X3) = k1_funct_1(X2,k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23])])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0),k1_funct_1(esk7_0,esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29]),c_0_23])])).

cnf(c_0_41,plain,
    ( v1_funct_1(k4_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0)) != esk6_0
    | k1_funct_1(X1,X2) != esk6_0
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))),X1)
    | ~ r2_hidden(esk6_0,k1_relat_1(k2_funct_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29]),c_0_23]),c_0_38])])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(X1,X2),X3),X4)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,esk1_3(X4,k2_relat_1(X4),X3)),X1)
    | ~ r2_hidden(X3,k2_relat_1(X4)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0)),esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0)),k4_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_23])])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(k4_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_29]),c_0_23])])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(k4_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_42]),c_0_29]),c_0_23])])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk7_0),esk6_0),esk6_0),esk7_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(k2_funct_1(esk7_0)))
    | ~ r2_hidden(k4_tarski(X2,esk6_0),X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_26]),c_0_29]),c_0_23])])]),c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(esk7_0),k1_funct_1(esk7_0,esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0))),esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(esk7_0),esk6_0),esk6_0),esk7_0)
    | ~ r2_hidden(esk6_0,k1_relat_1(k4_relat_1(esk7_0)))
    | ~ r2_hidden(k4_tarski(X2,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_46]),c_0_42]),c_0_29]),c_0_23])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,k1_funct_1(k4_relat_1(esk7_0),k1_funct_1(esk7_0,esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0)))),k4_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_49]),c_0_23])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk6_0,X2),k4_relat_1(esk7_0))
    | ~ r2_hidden(esk6_0,k1_relat_1(k4_relat_1(esk7_0)))
    | ~ r2_hidden(k4_tarski(X2,esk6_0),esk7_0)
    | ~ r2_hidden(k4_tarski(X3,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_26]),c_0_46]),c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(k4_relat_1(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_51]),c_0_47])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(esk6_0,X2),k4_relat_1(esk7_0))
    | ~ r2_hidden(k4_tarski(X2,esk6_0),esk7_0)
    | ~ r2_hidden(k4_tarski(X3,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_49])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_49]),c_0_29]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:58:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.83/1.07  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 0.83/1.07  # and selection function PSelectUnlessUniqMaxPos.
% 0.83/1.07  #
% 0.83/1.07  # Preprocessing time       : 0.028 s
% 0.83/1.07  # Presaturation interreduction done
% 0.83/1.07  
% 0.83/1.07  # Proof found!
% 0.83/1.07  # SZS status Theorem
% 0.83/1.07  # SZS output start CNFRefutation
% 0.83/1.07  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.83/1.07  fof(t20_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k2_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 0.83/1.07  fof(t57_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_funct_1)).
% 0.83/1.07  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.83/1.07  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.83/1.07  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_relat_1)).
% 0.83/1.07  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.83/1.07  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.83/1.07  fof(t23_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(X2))=>k1_funct_1(k5_relat_1(X2,X3),X1)=k1_funct_1(X3,k1_funct_1(X2,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 0.83/1.07  fof(c_0_9, plain, ![X5, X6, X7, X9, X10, X11, X12, X14]:(((~r2_hidden(X7,X6)|r2_hidden(k4_tarski(esk1_3(X5,X6,X7),X7),X5)|X6!=k2_relat_1(X5))&(~r2_hidden(k4_tarski(X10,X9),X5)|r2_hidden(X9,X6)|X6!=k2_relat_1(X5)))&((~r2_hidden(esk2_2(X11,X12),X12)|~r2_hidden(k4_tarski(X14,esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11))&(r2_hidden(esk2_2(X11,X12),X12)|r2_hidden(k4_tarski(esk3_2(X11,X12),esk2_2(X11,X12)),X11)|X12=k2_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.83/1.07  fof(c_0_10, plain, ![X25, X26, X27]:((r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(k4_tarski(X25,X26),X27)|~v1_relat_1(X27))&(r2_hidden(X26,k2_relat_1(X27))|~r2_hidden(k4_tarski(X25,X26),X27)|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_relat_1])])])).
% 0.83/1.07  cnf(c_0_11, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.83/1.07  fof(c_0_12, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k2_relat_1(X2)))=>(X1=k1_funct_1(X2,k1_funct_1(k2_funct_1(X2),X1))&X1=k1_funct_1(k5_relat_1(k2_funct_1(X2),X2),X1))))), inference(assume_negation,[status(cth)],[t57_funct_1])).
% 0.83/1.07  fof(c_0_13, plain, ![X33, X34, X35]:(((r2_hidden(X33,k1_relat_1(X35))|~r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(X34=k1_funct_1(X35,X33)|~r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(~r2_hidden(X33,k1_relat_1(X35))|X34!=k1_funct_1(X35,X33)|r2_hidden(k4_tarski(X33,X34),X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.83/1.07  cnf(c_0_14, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.83/1.07  cnf(c_0_15, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_11])).
% 0.83/1.07  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((v2_funct_1(esk7_0)&r2_hidden(esk6_0,k2_relat_1(esk7_0)))&(esk6_0!=k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))|esk6_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.83/1.07  fof(c_0_17, plain, ![X29]:((v1_relat_1(k2_funct_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(v1_funct_1(k2_funct_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.83/1.07  fof(c_0_18, plain, ![X16, X17, X18, X19, X20, X21]:(((~r2_hidden(k4_tarski(X18,X19),X17)|r2_hidden(k4_tarski(X19,X18),X16)|X17!=k4_relat_1(X16)|~v1_relat_1(X17)|~v1_relat_1(X16))&(~r2_hidden(k4_tarski(X21,X20),X16)|r2_hidden(k4_tarski(X20,X21),X17)|X17!=k4_relat_1(X16)|~v1_relat_1(X17)|~v1_relat_1(X16)))&((~r2_hidden(k4_tarski(esk4_2(X16,X17),esk5_2(X16,X17)),X17)|~r2_hidden(k4_tarski(esk5_2(X16,X17),esk4_2(X16,X17)),X16)|X17=k4_relat_1(X16)|~v1_relat_1(X17)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk4_2(X16,X17),esk5_2(X16,X17)),X17)|r2_hidden(k4_tarski(esk5_2(X16,X17),esk4_2(X16,X17)),X16)|X17=k4_relat_1(X16)|~v1_relat_1(X17)|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 0.83/1.07  fof(c_0_19, plain, ![X24]:(~v1_relat_1(X24)|v1_relat_1(k4_relat_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.83/1.07  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X1,X3),X2)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.83/1.07  cnf(c_0_21, plain, (r2_hidden(esk1_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.83/1.07  cnf(c_0_22, negated_conjecture, (r2_hidden(esk6_0,k2_relat_1(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.83/1.07  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.83/1.07  fof(c_0_24, plain, ![X28]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v2_funct_1(X28)|k2_funct_1(X28)=k4_relat_1(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.83/1.07  cnf(c_0_25, negated_conjecture, (esk6_0!=k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))|esk6_0!=k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.83/1.07  cnf(c_0_26, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.83/1.07  fof(c_0_27, plain, ![X30, X31, X32]:(~v1_relat_1(X31)|~v1_funct_1(X31)|(~v1_relat_1(X32)|~v1_funct_1(X32)|(~r2_hidden(X30,k1_relat_1(X31))|k1_funct_1(k5_relat_1(X31,X32),X30)=k1_funct_1(X32,k1_funct_1(X31,X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_funct_1])])])).
% 0.83/1.07  cnf(c_0_28, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.83/1.07  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.83/1.07  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k4_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.83/1.07  cnf(c_0_31, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.83/1.07  cnf(c_0_32, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_20])).
% 0.83/1.07  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0),k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.83/1.07  cnf(c_0_34, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.83/1.07  cnf(c_0_35, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.83/1.07  cnf(c_0_36, negated_conjecture, (k1_funct_1(k5_relat_1(k2_funct_1(esk7_0),esk7_0),esk6_0)!=esk6_0|k1_funct_1(X1,X2)!=esk6_0|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.83/1.07  cnf(c_0_37, plain, (k1_funct_1(k5_relat_1(X1,X2),X3)=k1_funct_1(X2,k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.83/1.07  cnf(c_0_38, negated_conjecture, (v1_relat_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_23])])).
% 0.83/1.07  cnf(c_0_39, plain, (r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X2,X1),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_31])).
% 0.83/1.07  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0),k1_funct_1(esk7_0,esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0))),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29]), c_0_23])])).
% 0.83/1.07  cnf(c_0_41, plain, (v1_funct_1(k4_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.83/1.07  cnf(c_0_42, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.83/1.07  cnf(c_0_43, negated_conjecture, (k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))!=esk6_0|k1_funct_1(X1,X2)!=esk6_0|~v1_funct_1(k2_funct_1(esk7_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,k1_funct_1(esk7_0,k1_funct_1(k2_funct_1(esk7_0),esk6_0))),X1)|~r2_hidden(esk6_0,k1_relat_1(k2_funct_1(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_29]), c_0_23]), c_0_38])])).
% 0.83/1.07  cnf(c_0_44, plain, (r2_hidden(k4_tarski(k1_funct_1(X1,X2),X3),X4)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,esk1_3(X4,k2_relat_1(X4),X3)),X1)|~r2_hidden(X3,k2_relat_1(X4))), inference(spm,[status(thm)],[c_0_15, c_0_26])).
% 0.83/1.07  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(esk7_0,esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0)),esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0)),k4_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_23])])).
% 0.83/1.07  cnf(c_0_46, negated_conjecture, (v1_funct_1(k4_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_29]), c_0_23])])).
% 0.83/1.07  cnf(c_0_47, negated_conjecture, (v1_relat_1(k4_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_42]), c_0_29]), c_0_23])])).
% 0.83/1.07  cnf(c_0_48, negated_conjecture, (~v1_funct_1(k2_funct_1(esk7_0))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(esk7_0),esk6_0),esk6_0),esk7_0)|~r2_hidden(esk6_0,k1_relat_1(k2_funct_1(esk7_0)))|~r2_hidden(k4_tarski(X2,esk6_0),X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_26]), c_0_29]), c_0_23])])]), c_0_26])).
% 0.83/1.07  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(esk7_0),k1_funct_1(esk7_0,esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0))),esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47]), c_0_22])])).
% 0.83/1.07  cnf(c_0_50, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(k1_funct_1(k4_relat_1(esk7_0),esk6_0),esk6_0),esk7_0)|~r2_hidden(esk6_0,k1_relat_1(k4_relat_1(esk7_0)))|~r2_hidden(k4_tarski(X2,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_35]), c_0_46]), c_0_42]), c_0_29]), c_0_23])])).
% 0.83/1.07  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,k1_funct_1(k4_relat_1(esk7_0),k1_funct_1(esk7_0,esk1_3(esk7_0,k2_relat_1(esk7_0),esk6_0)))),k4_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_49]), c_0_23])])).
% 0.83/1.07  cnf(c_0_52, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(esk6_0,X2),k4_relat_1(esk7_0))|~r2_hidden(esk6_0,k1_relat_1(k4_relat_1(esk7_0)))|~r2_hidden(k4_tarski(X2,esk6_0),esk7_0)|~r2_hidden(k4_tarski(X3,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_26]), c_0_46]), c_0_47])])).
% 0.83/1.07  cnf(c_0_53, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(k4_relat_1(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_51]), c_0_47])])).
% 0.83/1.07  cnf(c_0_54, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(esk6_0,X2),k4_relat_1(esk7_0))|~r2_hidden(k4_tarski(X2,esk6_0),esk7_0)|~r2_hidden(k4_tarski(X3,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.83/1.07  cnf(c_0_55, negated_conjecture, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_49])])).
% 0.83/1.07  cnf(c_0_56, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_49]), c_0_29]), c_0_23])]), ['proof']).
% 0.83/1.07  # SZS output end CNFRefutation
% 0.83/1.07  # Proof object total steps             : 57
% 0.83/1.07  # Proof object clause steps            : 38
% 0.83/1.07  # Proof object formula steps           : 19
% 0.83/1.07  # Proof object conjectures             : 25
% 0.83/1.07  # Proof object clause conjectures      : 22
% 0.83/1.07  # Proof object formula conjectures     : 3
% 0.83/1.07  # Proof object initial clauses used    : 15
% 0.83/1.07  # Proof object initial formulas used   : 9
% 0.83/1.07  # Proof object generating inferences   : 19
% 0.83/1.07  # Proof object simplifying inferences  : 52
% 0.83/1.07  # Training examples: 0 positive, 0 negative
% 0.83/1.07  # Parsed axioms                        : 9
% 0.83/1.07  # Removed by relevancy pruning/SinE    : 0
% 0.83/1.07  # Initial clauses                      : 23
% 0.83/1.07  # Removed in clause preprocessing      : 0
% 0.83/1.07  # Initial clauses in saturation        : 23
% 0.83/1.07  # Processed clauses                    : 1143
% 0.83/1.07  # ...of these trivial                  : 0
% 0.83/1.07  # ...subsumed                          : 328
% 0.83/1.07  # ...remaining for further processing  : 815
% 0.83/1.07  # Other redundant clauses eliminated   : 1190
% 0.83/1.07  # Clauses deleted for lack of memory   : 0
% 0.83/1.07  # Backward-subsumed                    : 60
% 0.83/1.07  # Backward-rewritten                   : 75
% 0.83/1.07  # Generated clauses                    : 46599
% 0.83/1.07  # ...of the previous two non-trivial   : 45407
% 0.83/1.07  # Contextual simplify-reflections      : 22
% 0.83/1.07  # Paramodulations                      : 45407
% 0.83/1.07  # Factorizations                       : 2
% 0.83/1.07  # Equation resolutions                 : 1190
% 0.83/1.07  # Propositional unsat checks           : 0
% 0.83/1.07  #    Propositional check models        : 0
% 0.83/1.07  #    Propositional check unsatisfiable : 0
% 0.83/1.07  #    Propositional clauses             : 0
% 0.83/1.07  #    Propositional clauses after purity: 0
% 0.83/1.07  #    Propositional unsat core size     : 0
% 0.83/1.07  #    Propositional preprocessing time  : 0.000
% 0.83/1.07  #    Propositional encoding time       : 0.000
% 0.83/1.07  #    Propositional solver time         : 0.000
% 0.83/1.07  #    Success case prop preproc time    : 0.000
% 0.83/1.07  #    Success case prop encoding time   : 0.000
% 0.83/1.07  #    Success case prop solver time     : 0.000
% 0.83/1.07  # Current number of processed clauses  : 654
% 0.83/1.07  #    Positive orientable unit clauses  : 47
% 0.83/1.07  #    Positive unorientable unit clauses: 0
% 0.83/1.07  #    Negative unit clauses             : 0
% 0.83/1.07  #    Non-unit-clauses                  : 607
% 0.83/1.07  # Current number of unprocessed clauses: 44272
% 0.83/1.07  # ...number of literals in the above   : 352878
% 0.83/1.07  # Current number of archived formulas  : 0
% 0.83/1.07  # Current number of archived clauses   : 156
% 0.83/1.07  # Clause-clause subsumption calls (NU) : 171983
% 0.83/1.07  # Rec. Clause-clause subsumption calls : 25979
% 0.83/1.07  # Non-unit clause-clause subsumptions  : 410
% 0.83/1.07  # Unit Clause-clause subsumption calls : 2657
% 0.83/1.07  # Rewrite failures with RHS unbound    : 0
% 0.83/1.07  # BW rewrite match attempts            : 2107
% 0.83/1.07  # BW rewrite match successes           : 2
% 0.83/1.07  # Condensation attempts                : 0
% 0.83/1.07  # Condensation successes               : 0
% 0.83/1.07  # Termbank termtop insertions          : 1367732
% 0.83/1.07  
% 0.83/1.07  # -------------------------------------------------
% 0.83/1.07  # User time                : 0.697 s
% 0.83/1.07  # System time              : 0.027 s
% 0.83/1.07  # Total time               : 0.725 s
% 0.83/1.07  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
