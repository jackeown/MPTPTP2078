%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t113_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:58 EDT 2019

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 498 expanded)
%              Number of clauses        :   49 ( 262 expanded)
%              Number of leaves         :   12 ( 148 expanded)
%              Depth                    :   19
%              Number of atoms          :  167 (1669 expanded)
%              Number of equality atoms :   75 ( 650 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',d2_zfmisc_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',t6_boole)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',t7_boole)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',t7_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',dt_o_0_0_xboole_0)).

fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t113_zfmisc_1.p',t113_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14,X17,X18,X19,X20,X21,X22,X24,X25] :
      ( ( r2_hidden(esk3_4(X11,X12,X13,X14),X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( r2_hidden(esk4_4(X11,X12,X13,X14),X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( X14 = k4_tarski(esk3_4(X11,X12,X13,X14),esk4_4(X11,X12,X13,X14))
        | ~ r2_hidden(X14,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( ~ r2_hidden(X18,X11)
        | ~ r2_hidden(X19,X12)
        | X17 != k4_tarski(X18,X19)
        | r2_hidden(X17,X13)
        | X13 != k2_zfmisc_1(X11,X12) )
      & ( ~ r2_hidden(esk5_3(X20,X21,X22),X22)
        | ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X25,X21)
        | esk5_3(X20,X21,X22) != k4_tarski(X24,X25)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk6_3(X20,X21,X22),X20)
        | r2_hidden(esk5_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( r2_hidden(esk7_3(X20,X21,X22),X21)
        | r2_hidden(esk5_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) )
      & ( esk5_3(X20,X21,X22) = k4_tarski(esk6_3(X20,X21,X22),esk7_3(X20,X21,X22))
        | r2_hidden(esk5_3(X20,X21,X22),X22)
        | X22 = k2_zfmisc_1(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_7,plain,(
    ! [X28] :
      ( ~ v1_xboole_0(X28)
      | X28 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_8,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ v1_xboole_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X31] :
      ( X31 = k1_xboole_0
      | r2_hidden(esk8_1(X31),X31) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk8_1(X1),X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,
    ( ~ epred1_0
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(definition)).

cnf(c_0_21,plain,
    ( X1 = k2_zfmisc_1(X2,X3)
    | r2_hidden(esk5_3(X2,X3,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_17])).

fof(c_0_22,plain,
    ( ~ epred2_0
  <=> ! [X2] : ~ r2_hidden(X2,o_0_0_xboole_0) ),
    introduced(definition)).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( epred1_0
    | ~ v1_xboole_0(X1) ),
    inference(split_equiv,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( X1 = k2_zfmisc_1(o_0_0_xboole_0,X2)
    | r2_hidden(esk5_3(o_0_0_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12])).

cnf(c_0_26,plain,
    ( ~ epred2_0
    | ~ epred1_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_23]),c_0_20]),c_0_22])).

cnf(c_0_27,plain,
    ( epred1_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_12])).

cnf(c_0_28,plain,
    ( X1 = k2_zfmisc_1(o_0_0_xboole_0,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_25])).

cnf(c_0_29,plain,
    ( ~ epred2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

fof(c_0_30,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_12])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_22]),c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_34,negated_conjecture,
    ( ( esk1_0 != k1_xboole_0
      | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 )
    & ( esk2_0 != k1_xboole_0
      | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
      | esk1_0 = k1_xboole_0
      | esk2_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_30])])])])).

cnf(c_0_35,plain,
    ( X1 != o_0_0_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_31]),c_0_32])).

cnf(c_0_36,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( X1 != o_0_0_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = k1_xboole_0
    | esk1_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != o_0_0_xboole_0
    | esk2_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_16]),c_0_16])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | X2 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( esk1_0 != k1_xboole_0
    | k2_zfmisc_1(esk1_0,esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( X1 != o_0_0_xboole_0
    | ~ r2_hidden(X2,k2_zfmisc_1(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = o_0_0_xboole_0
    | esk2_0 = o_0_0_xboole_0
    | esk1_0 = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_16]),c_0_16]),c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) != o_0_0_xboole_0
    | esk1_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_16]),c_0_16])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | X1 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = o_0_0_xboole_0
    | esk1_0 = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 != o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_50,plain,
    ( ~ epred4_0
  <=> ! [X2] : X2 != o_0_0_xboole_0 ),
    introduced(definition)).

fof(c_0_51,plain,
    ( ~ epred3_0
  <=> ! [X4,X3,X1] :
        ( ~ r2_hidden(X3,esk1_0)
        | ~ r2_hidden(X4,esk2_0)
        | X1 != k4_tarski(X3,X4) ) ),
    introduced(definition)).

cnf(c_0_52,plain,
    ( r2_hidden(X5,X6)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X5 != k4_tarski(X1,X3)
    | X6 != k2_zfmisc_1(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_53,negated_conjecture,
    ( k2_zfmisc_1(esk1_0,esk2_0) = o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( epred4_0
    | X1 != o_0_0_xboole_0 ),
    inference(split_equiv,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( ~ epred4_0
    | ~ epred3_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_35]),c_0_51]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( epred4_0 ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( ~ epred3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

fof(c_0_58,plain,
    ( ~ epred5_0
  <=> ! [X1] : ~ r2_hidden(X1,esk1_0) ),
    introduced(definition)).

fof(c_0_59,plain,
    ( ~ epred6_0
  <=> ! [X2] : ~ r2_hidden(X2,esk2_0) ),
    introduced(definition)).

cnf(c_0_60,negated_conjecture,
    ( X1 != k4_tarski(X2,X3)
    | ~ r2_hidden(X2,esk1_0)
    | ~ r2_hidden(X3,esk2_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_51]),c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( epred5_0
    | ~ r2_hidden(X1,esk1_0) ),
    inference(split_equiv,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( epred6_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_equiv,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( ~ epred6_0
    | ~ epred5_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(er,[status(thm)],[c_0_60]),c_0_58]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( epred5_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_19]),c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( epred6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_19]),c_0_45])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
