%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t205_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 177 expanded)
%              Number of clauses        :   29 (  81 expanded)
%              Number of leaves         :    8 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 519 expanded)
%              Number of equality atoms :   20 ( 119 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',existence_m1_subset_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',d4_relat_1)).

fof(t204_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> r2_hidden(X2,k11_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',t204_relat_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',t6_boole)).

fof(t205_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',t205_relat_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',t7_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t205_relat_1.p',dt_o_0_0_xboole_0)).

fof(c_0_8,plain,(
    ! [X31,X32] :
      ( ~ m1_subset_1(X31,X32)
      | v1_xboole_0(X32)
      | r2_hidden(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_9,plain,(
    ! [X24] : m1_subset_1(esk7_1(X24),X24) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk4_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk5_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk5_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk5_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk5_2(X19,X20),esk6_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r2_hidden(k4_tarski(X28,X29),X30)
        | r2_hidden(X29,k11_relat_1(X30,X28))
        | ~ v1_relat_1(X30) )
      & ( ~ r2_hidden(X29,k11_relat_1(X30,X28))
        | r2_hidden(k4_tarski(X28,X29),X30)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t204_relat_1])])])).

cnf(c_0_12,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | ~ r2_hidden(X1,k11_relat_1(X2,X3))
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X33] :
      ( ~ v1_xboole_0(X33)
      | X33 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v1_xboole_0(k11_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X2,esk7_1(k11_relat_1(X1,X2))),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k1_relat_1(X2))
        <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t205_relat_1])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_xboole_0(k11_relat_1(X1,X2))
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_23,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & ( ~ r2_hidden(esk1_0,k1_relat_1(esk2_0))
      | k11_relat_1(esk2_0,esk1_0) = k1_xboole_0 )
    & ( r2_hidden(esk1_0,k1_relat_1(esk2_0))
      | k11_relat_1(esk2_0,esk1_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_24,plain,
    ( k11_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk2_0))
    | k11_relat_1(esk2_0,esk1_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( k11_relat_1(esk2_0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_28,plain,(
    ! [X34,X35] :
      ( ~ r2_hidden(X34,X35)
      | ~ v1_xboole_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_29,negated_conjecture,
    ( k11_relat_1(esk2_0,esk1_0) = k1_xboole_0
    | ~ r2_hidden(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_32,plain,
    ( r2_hidden(X2,k11_relat_1(X3,X1))
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k11_relat_1(esk2_0,esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_30])])).

cnf(c_0_35,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(k4_tarski(esk1_0,X1),esk2_0)
    | ~ r2_hidden(esk1_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_29]),c_0_25])])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(k11_relat_1(X1,X2))
    | ~ r2_hidden(k4_tarski(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,X1),esk2_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_34]),c_0_25])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(k4_tarski(esk1_0,X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_30])])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_34]),c_0_40]),c_0_25])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_30])]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
