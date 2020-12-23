%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t174_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:54 EDT 2019

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 320 expanded)
%              Number of clauses        :   57 ( 157 expanded)
%              Number of leaves         :   17 (  97 expanded)
%              Depth                    :   18
%              Number of atoms          :  210 ( 761 expanded)
%              Number of equality atoms :   32 (  97 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',existence_m1_subset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',t2_subset)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',t8_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',dt_o_0_0_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',t166_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',d3_tarski)).

fof(t174_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k2_relat_1(X2))
          & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',t174_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',t3_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',t6_boole)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t174_relat_1.p',d5_relat_1)).

fof(c_0_11,plain,(
    ! [X43,X44,X45] :
      ( ~ r2_hidden(X43,X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X45))
      | ~ v1_xboole_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_12,plain,(
    ! [X27] : m1_subset_1(esk7_1(X27),X27) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_13,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X36,X37)
      | v1_xboole_0(X37)
      | r2_hidden(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_14,plain,(
    ! [X49,X50] :
      ( ~ v1_xboole_0(X49)
      | X49 = X50
      | ~ v1_xboole_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk7_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_22,plain,
    ( o_0_0_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( v1_xboole_0(esk7_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,
    ( ~ epred3_0
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(definition)).

fof(c_0_25,plain,
    ( ~ epred4_0
  <=> ! [X2] : ~ r2_hidden(X2,o_0_0_xboole_0) ),
    introduced(definition)).

cnf(c_0_26,plain,
    ( esk7_1(k1_zfmisc_1(X1)) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( epred3_0
    | ~ v1_xboole_0(X1) ),
    inference(split_equiv,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( ~ epred4_0
    | ~ epred3_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_26]),c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( epred3_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_19])).

fof(c_0_30,plain,(
    ! [X29,X30,X31,X33] :
      ( ( r2_hidden(esk8_3(X29,X30,X31),k2_relat_1(X31))
        | ~ r2_hidden(X29,k10_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(k4_tarski(X29,esk8_3(X29,X30,X31)),X31)
        | ~ r2_hidden(X29,k10_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk8_3(X29,X30,X31),X30)
        | ~ r2_hidden(X29,k10_relat_1(X31,X30))
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(X33,k2_relat_1(X31))
        | ~ r2_hidden(k4_tarski(X29,X33),X31)
        | ~ r2_hidden(X33,X30)
        | r2_hidden(X29,k10_relat_1(X31,X30))
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_31,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk3_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk3_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_32,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( X1 != k1_xboole_0
            & r1_tarski(X1,k2_relat_1(X2))
            & k10_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t174_relat_1])).

cnf(c_0_33,plain,
    ( ~ epred4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_34,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & esk1_0 != k1_xboole_0
    & r1_tarski(esk1_0,k2_relat_1(esk2_0))
    & k10_relat_1(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_32])])])).

fof(c_0_37,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_25]),c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(esk8_3(esk3_2(k10_relat_1(X1,X2),X3),X2,X1),X2)
    | r1_tarski(k10_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_42,plain,(
    ! [X46] :
      ( ~ v1_xboole_0(X46)
      | X46 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(k10_relat_1(X1,o_0_0_xboole_0),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_45,plain,
    ( ~ epred5_0
  <=> ! [X2] : ~ v1_xboole_0(X2) ),
    introduced(definition)).

fof(c_0_46,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(esk4_3(X15,X16,X17),X17),X15)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(esk5_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk5_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) )
      & ( r2_hidden(esk5_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk6_2(X21,X22),esk5_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k2_relat_1(esk2_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X3,k10_relat_1(X2,X4))
    | ~ r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,X4)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,
    ( ~ epred6_0
  <=> ! [X1,X3] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X3,k10_relat_1(X1,o_0_0_xboole_0)) ) ),
    introduced(definition)).

cnf(c_0_51,plain,
    ( m1_subset_1(k10_relat_1(X1,o_0_0_xboole_0),k1_zfmisc_1(X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( epred5_0
    | ~ v1_xboole_0(X1) ),
    inference(split_equiv,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(k4_tarski(esk4_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_2(esk1_0,X1),k2_relat_1(esk2_0))
    | r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | r1_tarski(X3,X4)
    | ~ r2_hidden(k4_tarski(X1,esk3_2(X3,X4)),X2)
    | ~ r2_hidden(esk3_2(X3,X4),k2_relat_1(X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( k10_relat_1(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_57,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_59,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk6_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( ~ epred6_0
    | ~ epred5_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_51]),c_0_45]),c_0_50])).

cnf(c_0_61,plain,
    ( epred5_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(X1,k2_relat_1(esk2_0),esk3_2(esk1_0,X2)),esk3_2(esk1_0,X2)),X1)
    | r1_tarski(esk1_0,X2)
    | k2_relat_1(esk2_0) != k2_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk1_0,X1)
    | ~ r2_hidden(k4_tarski(X2,esk3_2(esk1_0,X1)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_56]),c_0_57]),c_0_58])]),c_0_38])).

cnf(c_0_64,plain,
    ( X1 = k2_relat_1(esk7_1(k1_zfmisc_1(X2)))
    | r2_hidden(esk5_2(esk7_1(k1_zfmisc_1(X2)),X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_59])).

cnf(c_0_65,plain,
    ( ~ epred6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk1_0,X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_62]),c_0_63])).

fof(c_0_67,plain,
    ( ~ epred70_0
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(definition)).

cnf(c_0_68,plain,
    ( k2_relat_1(esk7_1(k1_zfmisc_1(X1))) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_64])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k10_relat_1(X2,o_0_0_xboole_0))
    | ~ v1_relat_1(X2) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_50]),c_0_65])).

fof(c_0_70,plain,
    ( ~ epred71_0
  <=> ! [X2] : ~ r2_hidden(X2,esk1_0) ),
    introduced(definition)).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( epred70_0
    | ~ v1_xboole_0(X1) ),
    inference(split_equiv,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_26])).

cnf(c_0_74,plain,
    ( v1_xboole_0(k10_relat_1(X1,o_0_0_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( ~ epred71_0
    | ~ epred70_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_71]),c_0_67]),c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( epred70_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_19])).

cnf(c_0_77,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( ~ epred71_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_79,negated_conjecture,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_hidden(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_70]),c_0_78])).

cnf(c_0_82,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk5_2(o_0_0_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_59]),c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( esk1_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_80,c_0_57])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
