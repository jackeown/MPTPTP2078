%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t142_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 151.49s
% Output     : CNFRefutation 151.49s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 142 expanded)
%              Number of clauses        :   41 (  67 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :  181 ( 547 expanded)
%              Number of equality atoms :   43 ( 153 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t142_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t142_funct_1.p',t142_funct_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t142_funct_1.p',d5_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t142_funct_1.p',d14_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t142_funct_1.p',d1_tarski)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t142_funct_1.p',t7_boole)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t142_funct_1.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t142_funct_1.p',dt_o_0_0_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
        <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_1])).

fof(c_0_8,plain,(
    ! [X33,X34,X35,X37,X38,X39,X40,X42] :
      ( ( ~ r2_hidden(X35,X34)
        | r2_hidden(k4_tarski(esk8_3(X33,X34,X35),X35),X33)
        | X34 != k2_relat_1(X33) )
      & ( ~ r2_hidden(k4_tarski(X38,X37),X33)
        | r2_hidden(X37,X34)
        | X34 != k2_relat_1(X33) )
      & ( ~ r2_hidden(esk9_2(X39,X40),X40)
        | ~ r2_hidden(k4_tarski(X42,esk9_2(X39,X40)),X39)
        | X40 = k2_relat_1(X39) )
      & ( r2_hidden(esk9_2(X39,X40),X40)
        | r2_hidden(k4_tarski(esk10_2(X39,X40),esk9_2(X39,X40)),X39)
        | X40 = k2_relat_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( ~ r2_hidden(esk1_0,k2_relat_1(esk2_0))
      | k10_relat_1(esk2_0,k1_tarski(esk1_0)) = k1_xboole_0 )
    & ( r2_hidden(esk1_0,k2_relat_1(esk2_0))
      | k10_relat_1(esk2_0,k1_tarski(esk1_0)) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(k4_tarski(X13,esk3_4(X10,X11,X12,X13)),X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk3_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X10)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k10_relat_1(X10,X11)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(esk4_3(X10,X17,X18),X18)
        | ~ r2_hidden(k4_tarski(esk4_3(X10,X17,X18),X20),X10)
        | ~ r2_hidden(X20,X17)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk4_3(X10,X17,X18),esk5_3(X10,X17,X18)),X10)
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk5_3(X10,X17,X18),X17)
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k10_relat_1(X10,X17)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X22
        | X23 != k1_tarski(X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_tarski(X22) )
      & ( ~ r2_hidden(esk6_2(X26,X27),X27)
        | esk6_2(X26,X27) != X26
        | X27 = k1_tarski(X26) )
      & ( r2_hidden(esk6_2(X26,X27),X27)
        | esk6_2(X26,X27) = X26
        | X27 = k1_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r2_hidden(esk1_0,k2_relat_1(esk2_0))
    | k10_relat_1(esk2_0,k1_tarski(esk1_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(esk4_3(X1,X2,X3),esk5_3(X1,X2,X3)),X1)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0),esk5_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0)),esk2_0)
    | r2_hidden(esk4_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk5_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0),k1_tarski(esk1_0))
    | r2_hidden(esk4_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_17]),c_0_15])])])).

fof(c_0_22,plain,(
    ! [X51,X52] :
      ( ~ r2_hidden(X51,X52)
      | ~ v1_xboole_0(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk5_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0),k2_relat_1(esk2_0))
    | r2_hidden(esk4_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk5_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0) = esk1_0
    | r2_hidden(esk4_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_0,k1_tarski(esk1_0),k1_xboole_0),k1_xboole_0)
    | r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_27,plain,(
    ! [X50] :
      ( ~ v1_xboole_0(X50)
      | X50 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk8_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk1_0,k2_relat_1(esk2_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk8_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_0,k2_relat_1(esk2_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ v1_relat_1(X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_3(esk2_0,k2_relat_1(esk2_0),esk1_0),esk1_0),esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk8_3(esk2_0,k2_relat_1(esk2_0),esk1_0),k10_relat_1(esk2_0,X1))
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_15])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk8_3(esk2_0,k2_relat_1(esk2_0),esk1_0),k10_relat_1(esk2_0,k1_tarski(esk1_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_tarski(esk1_0)) = k1_xboole_0
    | ~ r2_hidden(esk1_0,k2_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_41,plain,
    ( ~ epred13_0
  <=> ! [X2] : ~ v1_xboole_0(X2) ),
    introduced(definition)).

fof(c_0_42,plain,
    ( ~ epred12_0
  <=> ! [X1] :
        ( ~ v1_xboole_0(X1)
        | ~ v1_xboole_0(k1_xboole_0) ) ),
    introduced(definition)).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(k10_relat_1(esk2_0,k1_tarski(esk1_0)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_tarski(esk1_0)) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( epred13_0
    | ~ v1_xboole_0(X1) ),
    inference(split_equiv,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_47,negated_conjecture,
    ( ~ epred13_0
    | ~ epred12_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( epred13_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( ~ epred12_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])])).

fof(c_0_50,plain,
    ( ~ epred14_0
  <=> ! [X2] : ~ v1_xboole_0(X2) ),
    introduced(definition)).

fof(c_0_51,plain,
    ( ~ epred15_0
  <=> ! [X1] : ~ v1_xboole_0(X1) ),
    introduced(definition)).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_42]),c_0_49])).

cnf(c_0_53,negated_conjecture,
    ( epred14_0
    | ~ v1_xboole_0(X1) ),
    inference(split_equiv,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ epred15_0
    | ~ epred14_0 ),
    inference(apply_def,[status(thm)],[inference(apply_def,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_30]),c_0_50]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( epred14_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( ~ epred15_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(sr,[status(thm)],[inference(split_equiv,[status(thm)],[c_0_51]),c_0_56])).

cnf(c_0_58,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_46,c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
