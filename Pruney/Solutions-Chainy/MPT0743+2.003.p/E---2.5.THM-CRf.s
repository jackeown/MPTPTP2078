%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:15 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 211 expanded)
%              Number of clauses        :   44 (  95 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 563 expanded)
%              Number of equality atoms :   24 ( 104 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_14,plain,(
    ! [X25] : k1_ordinal1(X25) = k2_xboole_0(X25,k1_tarski(X25)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_15,plain,(
    ! [X22] : k2_tarski(X22,X22) = k1_tarski(X22) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ( ~ r2_hidden(esk2_0,esk3_0)
      | ~ r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X26,X27] :
      ( ( ~ r1_ordinal1(X26,X27)
        | r1_tarski(X26,X27)
        | ~ v3_ordinal1(X26)
        | ~ v3_ordinal1(X27) )
      & ( ~ r1_tarski(X26,X27)
        | r1_ordinal1(X26,X27)
        | ~ v3_ordinal1(X26)
        | ~ v3_ordinal1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k2_tarski(X1,X1)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_22,plain,(
    ! [X30] :
      ( ~ v3_ordinal1(X30)
      | v3_ordinal1(k1_ordinal1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_ordinal1(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X23,X24] :
      ( ( ~ r1_tarski(k1_tarski(X23),X24)
        | r2_hidden(X23,X24) )
      & ( ~ r2_hidden(X23,X24)
        | r1_tarski(k1_tarski(X23),X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_28,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k2_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X14)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk1_3(X14,X15,X16),X15)
        | ~ r2_hidden(esk1_3(X14,X15,X16),X16)
        | X16 = k2_xboole_0(X14,X15) )
      & ( r2_hidden(esk1_3(X14,X15,X16),X16)
        | r2_hidden(esk1_3(X14,X15,X16),X14)
        | r2_hidden(esk1_3(X14,X15,X16),X15)
        | X16 = k2_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ~ r1_tarski(X18,X19)
      | k2_xboole_0(X18,X19) = X19 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0)
    | r2_hidden(esk2_0,esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_33,plain,(
    ! [X7,X8] : k2_xboole_0(X7,X8) = k2_xboole_0(X8,X7) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X20,X21] : r1_tarski(X20,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0)
    | r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_39,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k2_tarski(X1,X1),X2) ),
    inference(rw,[status(thm)],[c_0_34,c_0_18])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_42,plain,(
    ! [X28,X29] :
      ( ~ v3_ordinal1(X28)
      | ~ v3_ordinal1(X29)
      | r1_ordinal1(X28,X29)
      | r2_hidden(X29,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k2_xboole_0(esk3_0,k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0))) = esk3_0
    | r2_hidden(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_xboole_0(k2_tarski(X1,X1),X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

fof(c_0_50,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ r1_tarski(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( r1_ordinal1(X1,esk3_0)
    | r2_hidden(esk3_0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_ordinal1(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_48]),c_0_49])])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_51,c_0_18])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_58,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( r1_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)),esk3_0)
    | r2_hidden(esk3_0,k2_xboole_0(X1,k2_tarski(X1,X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_ordinal1(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_38])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k2_tarski(X2,X2))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_32]),c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k2_tarski(esk2_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_43]),c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_64]),c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.19/0.41  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.19/0.41  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.19/0.41  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.19/0.41  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.19/0.41  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.19/0.41  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.41  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.19/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.41  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.19/0.41  fof(c_0_13, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 0.19/0.41  fof(c_0_14, plain, ![X25]:k1_ordinal1(X25)=k2_xboole_0(X25,k1_tarski(X25)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.19/0.41  fof(c_0_15, plain, ![X22]:k2_tarski(X22,X22)=k1_tarski(X22), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_16, negated_conjecture, (v3_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&((~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k1_ordinal1(esk2_0),esk3_0))&(r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k1_ordinal1(esk2_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.19/0.41  cnf(c_0_17, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_18, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  fof(c_0_19, plain, ![X26, X27]:((~r1_ordinal1(X26,X27)|r1_tarski(X26,X27)|(~v3_ordinal1(X26)|~v3_ordinal1(X27)))&(~r1_tarski(X26,X27)|r1_ordinal1(X26,X27)|(~v3_ordinal1(X26)|~v3_ordinal1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.19/0.41  cnf(c_0_20, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k1_ordinal1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_21, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k2_tarski(X1,X1))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.41  fof(c_0_22, plain, ![X30]:(~v3_ordinal1(X30)|v3_ordinal1(k1_ordinal1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.19/0.41  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_24, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.41  cnf(c_0_25, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_26, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  fof(c_0_27, plain, ![X23, X24]:((~r1_tarski(k1_tarski(X23),X24)|r2_hidden(X23,X24))&(~r2_hidden(X23,X24)|r1_tarski(k1_tarski(X23),X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.19/0.41  fof(c_0_28, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(r2_hidden(X12,X9)|r2_hidden(X12,X10))|X11!=k2_xboole_0(X9,X10))&((~r2_hidden(X13,X9)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))&(~r2_hidden(X13,X10)|r2_hidden(X13,X11)|X11!=k2_xboole_0(X9,X10))))&(((~r2_hidden(esk1_3(X14,X15,X16),X14)|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15))&(~r2_hidden(esk1_3(X14,X15,X16),X15)|~r2_hidden(esk1_3(X14,X15,X16),X16)|X16=k2_xboole_0(X14,X15)))&(r2_hidden(esk1_3(X14,X15,X16),X16)|(r2_hidden(esk1_3(X14,X15,X16),X14)|r2_hidden(esk1_3(X14,X15,X16),X15))|X16=k2_xboole_0(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.41  fof(c_0_29, plain, ![X18, X19]:(~r1_tarski(X18,X19)|k2_xboole_0(X18,X19)=X19), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0)|r2_hidden(esk2_0,esk3_0)|~v3_ordinal1(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.19/0.41  cnf(c_0_31, plain, (v3_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_26, c_0_21])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  fof(c_0_33, plain, ![X7, X8]:k2_xboole_0(X7,X8)=k2_xboole_0(X8,X7), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(X1,X2)|~r1_tarski(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  fof(c_0_35, plain, ![X20, X21]:r1_tarski(X20,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.41  cnf(c_0_36, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_37, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (r1_tarski(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0)|r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.41  cnf(c_0_39, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_40, plain, (r2_hidden(X1,X2)|~r1_tarski(k2_tarski(X1,X1),X2)), inference(rw,[status(thm)],[c_0_34, c_0_18])).
% 0.19/0.41  cnf(c_0_41, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.41  fof(c_0_42, plain, ![X28, X29]:(~v3_ordinal1(X28)|(~v3_ordinal1(X29)|(r1_ordinal1(X28,X29)|r2_hidden(X29,X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.19/0.41  cnf(c_0_43, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (k2_xboole_0(esk3_0,k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)))=esk3_0|r2_hidden(esk2_0,esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.19/0.41  cnf(c_0_45, plain, (r2_hidden(X1,k2_xboole_0(k2_tarski(X1,X1),X2))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.41  cnf(c_0_46, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k1_ordinal1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_48, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r2_hidden(X1,esk3_0)|~r2_hidden(X1,k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.41  cnf(c_0_49, plain, (r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_45, c_0_39])).
% 0.19/0.41  fof(c_0_50, plain, ![X31, X32]:(~r2_hidden(X31,X32)|~r1_tarski(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.41  cnf(c_0_51, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (r1_ordinal1(X1,esk3_0)|r2_hidden(esk3_0,X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_46, c_0_25])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_47, c_0_21])).
% 0.19/0.41  cnf(c_0_54, negated_conjecture, (r2_hidden(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_48]), c_0_49])])).
% 0.19/0.41  cnf(c_0_55, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.41  cnf(c_0_56, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_51, c_0_18])).
% 0.19/0.41  cnf(c_0_57, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  fof(c_0_58, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.19/0.41  cnf(c_0_59, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (r1_ordinal1(k2_xboole_0(X1,k2_tarski(X1,X1)),esk3_0)|r2_hidden(esk3_0,k2_xboole_0(X1,k2_tarski(X1,X1)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_52, c_0_31])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (~r1_ordinal1(k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54])])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk3_0,k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)))), inference(spm,[status(thm)],[c_0_55, c_0_38])).
% 0.19/0.41  cnf(c_0_63, plain, (~r2_hidden(X1,k2_tarski(X2,X2))|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.41  cnf(c_0_64, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_57])).
% 0.19/0.41  cnf(c_0_65, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.41  cnf(c_0_66, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_59])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(esk2_0,k2_tarski(esk2_0,esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_32]), c_0_61])).
% 0.19/0.41  cnf(c_0_68, negated_conjecture, (~r2_hidden(esk3_0,k2_tarski(esk2_0,esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_43]), c_0_63])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_64]), c_0_65])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 71
% 0.19/0.41  # Proof object clause steps            : 44
% 0.19/0.41  # Proof object formula steps           : 27
% 0.19/0.41  # Proof object conjectures             : 22
% 0.19/0.41  # Proof object clause conjectures      : 19
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 19
% 0.19/0.41  # Proof object initial formulas used   : 13
% 0.19/0.41  # Proof object generating inferences   : 18
% 0.19/0.41  # Proof object simplifying inferences  : 20
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 13
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 23
% 0.19/0.41  # Removed in clause preprocessing      : 2
% 0.19/0.41  # Initial clauses in saturation        : 21
% 0.19/0.41  # Processed clauses                    : 368
% 0.19/0.41  # ...of these trivial                  : 31
% 0.19/0.41  # ...subsumed                          : 181
% 0.19/0.41  # ...remaining for further processing  : 156
% 0.19/0.41  # Other redundant clauses eliminated   : 6
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 18
% 0.19/0.41  # Backward-rewritten                   : 12
% 0.19/0.41  # Generated clauses                    : 1546
% 0.19/0.41  # ...of the previous two non-trivial   : 1367
% 0.19/0.41  # Contextual simplify-reflections      : 2
% 0.19/0.41  # Paramodulations                      : 1465
% 0.19/0.41  # Factorizations                       : 60
% 0.19/0.41  # Equation resolutions                 : 10
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 115
% 0.19/0.41  #    Positive orientable unit clauses  : 23
% 0.19/0.41  #    Positive unorientable unit clauses: 1
% 0.19/0.41  #    Negative unit clauses             : 24
% 0.19/0.41  #    Non-unit-clauses                  : 67
% 0.19/0.41  # Current number of unprocessed clauses: 987
% 0.19/0.41  # ...number of literals in the above   : 3390
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 43
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 1459
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1068
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 122
% 0.19/0.41  # Unit Clause-clause subsumption calls : 334
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 20
% 0.19/0.41  # BW rewrite match successes           : 11
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 18177
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.059 s
% 0.19/0.41  # System time              : 0.007 s
% 0.19/0.41  # Total time               : 0.066 s
% 0.19/0.41  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
