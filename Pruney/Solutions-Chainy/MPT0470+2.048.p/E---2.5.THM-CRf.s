%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:01 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 778 expanded)
%              Number of clauses        :   60 ( 386 expanded)
%              Number of leaves         :   20 ( 231 expanded)
%              Depth                    :   20
%              Number of atoms          :  245 (1967 expanded)
%              Number of equality atoms :   52 ( 297 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(d7_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( X2 = k4_relat_1(X1)
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(involutiveness_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k4_relat_1(k4_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t54_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(c_0_18,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r2_hidden(esk2_2(X10,X11),X10)
        | r1_xboole_0(X10,X11) )
      & ( r2_hidden(esk2_2(X10,X11),X11)
        | r1_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_20,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r1_xboole_0(X16,X17)
        | r2_hidden(esk3_2(X16,X17),k3_xboole_0(X16,X17)) )
      & ( ~ r2_hidden(X21,k3_xboole_0(X19,X20))
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X22] :
      ( X22 = k1_xboole_0
      | r2_hidden(esk4_1(X22),X22) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_22,plain,
    ( ~ epred1_0
  <=> ! [X1,X2] : ~ r1_xboole_0(X1,X2) ),
    introduced(definition)).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( epred1_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_equiv,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,X25)
      | k3_xboole_0(X24,X25) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_30,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X40)
      | ~ v1_relat_1(X41)
      | r1_tarski(k2_relat_1(k5_relat_1(X40,X41)),k2_relat_1(X41)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

fof(c_0_31,plain,
    ( ~ epred2_0
  <=> ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    introduced(definition)).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( epred1_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_35,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( epred2_0
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(split_equiv,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_32]),c_0_22]),c_0_31])).

cnf(c_0_39,plain,
    ( epred1_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( k3_xboole_0(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) = k2_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,plain,
    ( epred2_0
    | r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_42,plain,
    ( ~ epred2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_43,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_40])).

cnf(c_0_44,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(sr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( k2_relat_1(k5_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

fof(c_0_47,plain,(
    ! [X26] :
      ( ~ v1_xboole_0(X26)
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_48,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_46]),c_0_44])).

cnf(c_0_50,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_51,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
      | k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).

fof(c_0_52,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( ( ~ r2_hidden(k4_tarski(X29,X30),X28)
        | r2_hidden(k4_tarski(X30,X29),X27)
        | X28 != k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X32,X31),X27)
        | r2_hidden(k4_tarski(X31,X32),X28)
        | X28 != k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X27,X28),esk6_2(X27,X28)),X28)
        | ~ r2_hidden(k4_tarski(esk6_2(X27,X28),esk5_2(X27,X28)),X27)
        | X28 = k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(k4_tarski(esk5_2(X27,X28),esk6_2(X27,X28)),X28)
        | r2_hidden(k4_tarski(esk6_2(X27,X28),esk5_2(X27,X28)),X27)
        | X28 = k4_relat_1(X27)
        | ~ v1_relat_1(X28)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).

fof(c_0_53,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | v1_relat_1(k4_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_54,plain,(
    ! [X39] :
      ( ~ v1_relat_1(X39)
      | k4_relat_1(k4_relat_1(X39)) = X39 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_34])])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(X2,X1),X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k4_relat_1(X3)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_60,plain,(
    ! [X44] :
      ( ~ v1_relat_1(X44)
      | r2_hidden(k4_tarski(esk7_1(X44),esk8_1(X44)),X44)
      | X44 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_61,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( epred2_0
    | r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_57])).

fof(c_0_64,plain,(
    ! [X38] :
      ( v1_xboole_0(X38)
      | ~ v1_relat_1(X38)
      | ~ v1_xboole_0(k2_relat_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

fof(c_0_65,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X36)
      | ~ v1_relat_1(X37)
      | v1_relat_1(k5_relat_1(X36,X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

cnf(c_0_66,plain,
    ( r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X2,X1),X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_58]),c_0_59])).

cnf(c_0_67,plain,
    ( r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( k4_relat_1(k4_relat_1(X1)) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_50])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_62])).

cnf(c_0_70,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[c_0_63,c_0_42])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k4_tarski(esk8_1(X1),esk7_1(X1)),k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,plain,
    ( k4_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_34])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_69]),c_0_70])])).

fof(c_0_76,plain,(
    ! [X9] :
      ( ~ v1_xboole_0(X9)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_77,plain,
    ( v1_xboole_0(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_78,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

fof(c_0_79,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X42)
      | ~ v1_relat_1(X43)
      | k4_relat_1(k5_relat_1(X42,X43)) = k5_relat_1(k4_relat_1(X43),k4_relat_1(X42)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).

cnf(c_0_80,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,plain,
    ( v1_xboole_0(k5_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_46]),c_0_34])])).

cnf(c_0_82,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_74])).

cnf(c_0_83,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_59])).

cnf(c_0_84,plain,
    ( k4_relat_1(k5_relat_1(X1,X2)) = k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,plain,
    ( k5_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k4_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_50])).

cnf(c_0_87,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_50]),c_0_34])])).

cnf(c_0_88,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
    | k5_relat_1(esk9_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_89,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X1)) = k4_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_90,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87]),c_0_34])])).

cnf(c_0_91,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_85]),c_0_56])])).

cnf(c_0_92,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(X1)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_87]),c_0_87]),c_0_90])])).

cnf(c_0_93,negated_conjecture,
    ( k4_relat_1(k4_relat_1(esk9_0)) = esk9_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_56])).

cnf(c_0_94,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk9_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_90])])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_relat_1(k4_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_59]),c_0_56])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.13/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.043 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.41  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.41  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.41  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.13/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.41  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 0.13/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.41  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.41  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.13/0.41  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.13/0.41  fof(d7_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(X2=k4_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>r2_hidden(k4_tarski(X4,X3),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_1)).
% 0.13/0.41  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.13/0.41  fof(involutiveness_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k4_relat_1(k4_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 0.13/0.41  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 0.13/0.41  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.13/0.41  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.41  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.41  fof(t54_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 0.13/0.41  fof(c_0_18, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.41  fof(c_0_19, plain, ![X10, X11, X13, X14, X15]:(((r2_hidden(esk2_2(X10,X11),X10)|r1_xboole_0(X10,X11))&(r2_hidden(esk2_2(X10,X11),X11)|r1_xboole_0(X10,X11)))&(~r2_hidden(X15,X13)|~r2_hidden(X15,X14)|~r1_xboole_0(X13,X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.41  fof(c_0_20, plain, ![X16, X17, X19, X20, X21]:((r1_xboole_0(X16,X17)|r2_hidden(esk3_2(X16,X17),k3_xboole_0(X16,X17)))&(~r2_hidden(X21,k3_xboole_0(X19,X20))|~r1_xboole_0(X19,X20))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.41  fof(c_0_21, plain, ![X22]:(X22=k1_xboole_0|r2_hidden(esk4_1(X22),X22)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.13/0.41  fof(c_0_22, plain, (~epred1_0<=>![X1, X2]:~r1_xboole_0(X1,X2)), introduced(definition)).
% 0.13/0.41  cnf(c_0_23, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.41  cnf(c_0_24, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_25, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.41  cnf(c_0_26, plain, (X1=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_27, plain, (epred1_0|~r1_xboole_0(X1,X2)), inference(split_equiv,[status(thm)],[c_0_22])).
% 0.13/0.41  cnf(c_0_28, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.41  fof(c_0_29, plain, ![X24, X25]:(~r1_tarski(X24,X25)|k3_xboole_0(X24,X25)=X24), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.41  fof(c_0_30, plain, ![X40, X41]:(~v1_relat_1(X40)|(~v1_relat_1(X41)|r1_tarski(k2_relat_1(k5_relat_1(X40,X41)),k2_relat_1(X41)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.13/0.41  fof(c_0_31, plain, (~epred2_0<=>![X3]:~r2_hidden(X3,k1_xboole_0)), introduced(definition)).
% 0.13/0.41  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.41  cnf(c_0_33, plain, (epred1_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.41  cnf(c_0_34, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.41  cnf(c_0_35, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.41  cnf(c_0_36, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.41  cnf(c_0_37, plain, (epred2_0|~r2_hidden(X1,k1_xboole_0)), inference(split_equiv,[status(thm)],[c_0_31])).
% 0.13/0.41  cnf(c_0_38, plain, (~epred2_0|~epred1_0), inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_32]), c_0_22]), c_0_31])).
% 0.13/0.41  cnf(c_0_39, plain, (epred1_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.41  cnf(c_0_40, plain, (k3_xboole_0(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))=k2_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.41  cnf(c_0_41, plain, (epred2_0|r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 0.13/0.41  cnf(c_0_42, plain, (~epred2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.13/0.41  cnf(c_0_43, plain, (k2_relat_1(k5_relat_1(X1,X2))=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_32, c_0_40])).
% 0.13/0.41  cnf(c_0_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.41  cnf(c_0_45, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(sr,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.41  cnf(c_0_46, plain, (k2_relat_1(k5_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.13/0.41  fof(c_0_47, plain, ![X26]:(~v1_xboole_0(X26)|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.13/0.41  fof(c_0_48, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.13/0.41  cnf(c_0_49, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_46]), c_0_44])).
% 0.13/0.41  cnf(c_0_50, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.41  fof(c_0_51, negated_conjecture, (v1_relat_1(esk9_0)&(k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_48])])])).
% 0.13/0.41  fof(c_0_52, plain, ![X27, X28, X29, X30, X31, X32]:(((~r2_hidden(k4_tarski(X29,X30),X28)|r2_hidden(k4_tarski(X30,X29),X27)|X28!=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27))&(~r2_hidden(k4_tarski(X32,X31),X27)|r2_hidden(k4_tarski(X31,X32),X28)|X28!=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27)))&((~r2_hidden(k4_tarski(esk5_2(X27,X28),esk6_2(X27,X28)),X28)|~r2_hidden(k4_tarski(esk6_2(X27,X28),esk5_2(X27,X28)),X27)|X28=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27))&(r2_hidden(k4_tarski(esk5_2(X27,X28),esk6_2(X27,X28)),X28)|r2_hidden(k4_tarski(esk6_2(X27,X28),esk5_2(X27,X28)),X27)|X28=k4_relat_1(X27)|~v1_relat_1(X28)|~v1_relat_1(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_relat_1])])])])])])).
% 0.13/0.41  fof(c_0_53, plain, ![X35]:(~v1_relat_1(X35)|v1_relat_1(k4_relat_1(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.13/0.41  fof(c_0_54, plain, ![X39]:(~v1_relat_1(X39)|k4_relat_1(k4_relat_1(X39))=X39), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k4_relat_1])])).
% 0.13/0.41  cnf(c_0_55, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_34])])).
% 0.13/0.41  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.41  cnf(c_0_57, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_58, plain, (r2_hidden(k4_tarski(X2,X1),X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k4_relat_1(X3)|~v1_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.41  cnf(c_0_59, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.41  fof(c_0_60, plain, ![X44]:(~v1_relat_1(X44)|(r2_hidden(k4_tarski(esk7_1(X44),esk8_1(X44)),X44)|X44=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.13/0.41  cnf(c_0_61, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.13/0.41  cnf(c_0_62, negated_conjecture, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.13/0.41  cnf(c_0_63, plain, (epred2_0|r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_57])).
% 0.13/0.41  fof(c_0_64, plain, ![X38]:(v1_xboole_0(X38)|~v1_relat_1(X38)|~v1_xboole_0(k2_relat_1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.13/0.41  fof(c_0_65, plain, ![X36, X37]:(~v1_relat_1(X36)|~v1_relat_1(X37)|v1_relat_1(k5_relat_1(X36,X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.41  cnf(c_0_66, plain, (r2_hidden(k4_tarski(X1,X2),k4_relat_1(X3))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X2,X1),X3)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_58]), c_0_59])).
% 0.13/0.41  cnf(c_0_67, plain, (r2_hidden(k4_tarski(esk7_1(X1),esk8_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.13/0.41  cnf(c_0_68, plain, (k4_relat_1(k4_relat_1(X1))=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_61, c_0_50])).
% 0.13/0.41  cnf(c_0_69, negated_conjecture, (k3_xboole_0(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_62])).
% 0.13/0.41  cnf(c_0_70, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(sr,[status(thm)],[c_0_63, c_0_42])).
% 0.13/0.41  cnf(c_0_71, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.41  cnf(c_0_72, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.41  cnf(c_0_73, plain, (X1=k1_xboole_0|r2_hidden(k4_tarski(esk8_1(X1),esk7_1(X1)),k4_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.13/0.41  cnf(c_0_74, plain, (k4_relat_1(k4_relat_1(k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_34])).
% 0.13/0.41  cnf(c_0_75, negated_conjecture, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_69]), c_0_70])])).
% 0.13/0.41  fof(c_0_76, plain, ![X9]:(~v1_xboole_0(X9)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.41  cnf(c_0_77, plain, (v1_xboole_0(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(k5_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.41  cnf(c_0_78, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0|~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.13/0.41  fof(c_0_79, plain, ![X42, X43]:(~v1_relat_1(X42)|(~v1_relat_1(X43)|k4_relat_1(k5_relat_1(X42,X43))=k5_relat_1(k4_relat_1(X43),k4_relat_1(X42)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t54_relat_1])])])).
% 0.13/0.41  cnf(c_0_80, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.41  cnf(c_0_81, plain, (v1_xboole_0(k5_relat_1(X1,k1_xboole_0))|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_46]), c_0_34])])).
% 0.13/0.41  cnf(c_0_82, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_59, c_0_74])).
% 0.13/0.41  cnf(c_0_83, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_78, c_0_59])).
% 0.13/0.41  cnf(c_0_84, plain, (k4_relat_1(k5_relat_1(X1,X2))=k5_relat_1(k4_relat_1(X2),k4_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.13/0.41  cnf(c_0_85, plain, (k5_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.13/0.41  cnf(c_0_86, plain, (v1_relat_1(k1_xboole_0)|~v1_xboole_0(k4_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_82, c_0_50])).
% 0.13/0.41  cnf(c_0_87, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_50]), c_0_34])])).
% 0.13/0.41  cnf(c_0_88, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|k5_relat_1(esk9_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.41  cnf(c_0_89, plain, (k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X1))=k4_relat_1(k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.13/0.41  cnf(c_0_90, plain, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87]), c_0_34])])).
% 0.13/0.41  cnf(c_0_91, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_85]), c_0_56])])).
% 0.13/0.41  cnf(c_0_92, plain, (k5_relat_1(k1_xboole_0,k4_relat_1(X1))=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_87]), c_0_87]), c_0_90])])).
% 0.13/0.41  cnf(c_0_93, negated_conjecture, (k4_relat_1(k4_relat_1(esk9_0))=esk9_0), inference(spm,[status(thm)],[c_0_61, c_0_56])).
% 0.13/0.41  cnf(c_0_94, negated_conjecture, (k5_relat_1(k1_xboole_0,esk9_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_90])])).
% 0.13/0.41  cnf(c_0_95, negated_conjecture, (~v1_relat_1(k4_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94])).
% 0.13/0.41  cnf(c_0_96, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_59]), c_0_56])]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 97
% 0.13/0.41  # Proof object clause steps            : 60
% 0.13/0.41  # Proof object formula steps           : 37
% 0.13/0.41  # Proof object conjectures             : 13
% 0.13/0.41  # Proof object clause conjectures      : 10
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 22
% 0.13/0.41  # Proof object initial formulas used   : 18
% 0.13/0.41  # Proof object generating inferences   : 31
% 0.13/0.41  # Proof object simplifying inferences  : 34
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 18
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 27
% 0.13/0.41  # Removed in clause preprocessing      : 0
% 0.13/0.41  # Initial clauses in saturation        : 27
% 0.13/0.41  # Processed clauses                    : 182
% 0.13/0.41  # ...of these trivial                  : 2
% 0.13/0.41  # ...subsumed                          : 42
% 0.13/0.41  # ...remaining for further processing  : 138
% 0.13/0.41  # Other redundant clauses eliminated   : 2
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 2
% 0.13/0.41  # Backward-rewritten                   : 22
% 0.13/0.41  # Generated clauses                    : 661
% 0.13/0.41  # ...of the previous two non-trivial   : 578
% 0.13/0.41  # Contextual simplify-reflections      : 9
% 0.13/0.41  # Paramodulations                      : 654
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 2
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 82
% 0.13/0.41  #    Positive orientable unit clauses  : 13
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 4
% 0.13/0.41  #    Non-unit-clauses                  : 65
% 0.13/0.41  # Current number of unprocessed clauses: 430
% 0.13/0.41  # ...number of literals in the above   : 1870
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 53
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 1121
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 760
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 51
% 0.13/0.41  # Unit Clause-clause subsumption calls : 74
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 5
% 0.13/0.41  # BW rewrite match successes           : 5
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 11744
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.068 s
% 0.13/0.41  # System time              : 0.004 s
% 0.13/0.41  # Total time               : 0.072 s
% 0.13/0.41  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
