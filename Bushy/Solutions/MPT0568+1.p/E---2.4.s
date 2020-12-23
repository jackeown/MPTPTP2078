%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t172_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:54 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 199 expanded)
%              Number of clauses        :   39 ( 104 expanded)
%              Number of leaves         :   10 (  52 expanded)
%              Depth                    :   27
%              Number of atoms          :  155 ( 671 expanded)
%              Number of equality atoms :   28 ( 102 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',d14_relat_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',existence_m1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',t6_boole)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',cc1_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',fc1_xboole_0)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',t8_boole)).

fof(dt_o_1_6_relat_1,axiom,(
    ! [X1] : m1_subset_1(o_1_6_relat_1(X1),k10_relat_1(k1_xboole_0,X1)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',dt_o_1_6_relat_1)).

fof(t172_relat_1,conjecture,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/relat_1__t172_relat_1.p',t172_relat_1)).

fof(c_0_10,plain,(
    ! [X9,X10,X11,X12,X14,X15,X16,X17,X19] :
      ( ( r2_hidden(k4_tarski(X12,esk2_4(X9,X10,X11,X12)),X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk2_4(X9,X10,X11,X12),X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),X9)
        | ~ r2_hidden(X15,X10)
        | r2_hidden(X14,X11)
        | X11 != k10_relat_1(X9,X10)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(esk3_3(X9,X16,X17),X17)
        | ~ r2_hidden(k4_tarski(esk3_3(X9,X16,X17),X19),X9)
        | ~ r2_hidden(X19,X16)
        | X17 = k10_relat_1(X9,X16)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(esk3_3(X9,X16,X17),esk4_3(X9,X16,X17)),X9)
        | r2_hidden(esk3_3(X9,X16,X17),X17)
        | X17 = k10_relat_1(X9,X16)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk4_3(X9,X16,X17),X16)
        | r2_hidden(esk3_3(X9,X16,X17),X17)
        | X17 = k10_relat_1(X9,X16)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ v1_xboole_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k10_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_14,plain,(
    ! [X22] : m1_subset_1(esk5_1(X22),X22) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk2_4(X1,X2,k10_relat_1(X1,X2),X3),X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k10_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X28] :
      ( ~ v1_xboole_0(X28)
      | X28 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k10_relat_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k10_relat_1(X1,X2))
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X33] :
      ( ~ v1_xboole_0(X33)
      | v1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

cnf(c_0_25,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_27]),c_0_26])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X4,k10_relat_1(X3,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_16])).

cnf(c_0_30,plain,
    ( v1_xboole_0(k10_relat_1(X1,k1_xboole_0))
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_21])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_32,plain,(
    ! [X31,X32] :
      ( ~ v1_xboole_0(X31)
      | X31 = X32
      | ~ v1_xboole_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k10_relat_1(X1,k1_xboole_0))
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k10_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_36,plain,
    ( X1 = k10_relat_1(X2,k1_xboole_0)
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X2,k1_xboole_0)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_38,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X2,k1_xboole_0)
    | ~ v1_xboole_0(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

fof(c_0_39,plain,(
    ! [X21] : m1_subset_1(o_1_6_relat_1(X21),k10_relat_1(k1_xboole_0,X21)) ),
    inference(variable_rename,[status(thm)],[dt_o_1_6_relat_1])).

cnf(c_0_40,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k10_relat_1(X2,k1_xboole_0)
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_41,plain,
    ( m1_subset_1(o_1_6_relat_1(X1),k10_relat_1(k1_xboole_0,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_42,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k10_relat_1(X2,k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_40]),c_0_31])]),c_0_26])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k10_relat_1(k1_xboole_0,X1))
    | r2_hidden(o_1_6_relat_1(X1),k10_relat_1(k1_xboole_0,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_41])).

cnf(c_0_44,plain,
    ( v1_xboole_0(k10_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_31])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(k10_relat_1(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_46,plain,
    ( k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_45])).

cnf(c_0_47,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_46]),c_0_31])])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X1,esk2_4(X2,X3,X4,X1)),X2)
    | ~ r2_hidden(X1,X4)
    | X4 != k10_relat_1(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_26]),c_0_31])])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X1,esk2_4(X2,X3,k10_relat_1(X2,X3),X1)),X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k10_relat_1(X2,X3)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_51,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X1,k10_relat_1(k1_xboole_0,X2)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_52,negated_conjecture,(
    ~ ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t172_relat_1])).

cnf(c_0_53,plain,
    ( v1_xboole_0(k10_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_21])).

fof(c_0_54,negated_conjecture,(
    k10_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_52])])])).

cnf(c_0_55,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( k10_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_57,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_26]),c_0_31])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])]),
    [proof]).
%------------------------------------------------------------------------------
