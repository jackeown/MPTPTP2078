%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t14_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:16 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 352 expanded)
%              Number of clauses        :   33 ( 148 expanded)
%              Number of leaves         :    6 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :  155 (1639 expanded)
%              Number of equality atoms :   55 ( 648 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t14_funct_1.p',d5_funct_1)).

fof(t14_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t14_funct_1.p',t14_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t14_funct_1.p',d1_tarski)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t14_funct_1.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t14_funct_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t14_funct_1.p',existence_m1_subset_1)).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X20,X21,X22,X24] :
      ( ( r2_hidden(esk4_3(X16,X17,X18),k1_relat_1(X16))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X18 = k1_funct_1(X16,esk4_3(X16,X17,X18))
        | ~ r2_hidden(X18,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X21,k1_relat_1(X16))
        | X20 != k1_funct_1(X16,X21)
        | r2_hidden(X20,X17)
        | X17 != k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(esk5_2(X16,X22),X22)
        | ~ r2_hidden(X24,k1_relat_1(X16))
        | esk5_2(X16,X22) != k1_funct_1(X16,X24)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk6_2(X16,X22),k1_relat_1(X16))
        | r2_hidden(esk5_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( esk5_2(X16,X22) = k1_funct_1(X16,esk6_2(X16,X22))
        | r2_hidden(esk5_2(X16,X22),X22)
        | X22 = k2_relat_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( k1_relat_1(X2) = k1_tarski(X1)
         => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t14_funct_1])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X9
        | X10 != k1_tarski(X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k1_tarski(X9) )
      & ( ~ r2_hidden(esk3_2(X13,X14),X14)
        | esk3_2(X13,X14) != X13
        | X14 = k1_tarski(X13) )
      & ( r2_hidden(esk3_2(X13,X14),X14)
        | esk3_2(X13,X14) = X13
        | X14 = k1_tarski(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & k1_relat_1(esk2_0) = k1_tarski(esk1_0)
    & k2_relat_1(esk2_0) != k1_tarski(k1_funct_1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X36,X37] :
      ( ~ r2_hidden(X36,X37)
      | ~ v1_xboole_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( k1_relat_1(esk2_0) = k1_tarski(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

cnf(c_0_20,plain,
    ( X1 = k1_funct_1(X2,esk4_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_3(esk2_0,k2_relat_1(esk2_0),X1),k1_tarski(esk1_0))
    | ~ r2_hidden(X1,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_23,plain,
    ( ~ v1_xboole_0(k2_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( k1_funct_1(X1,esk4_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( esk4_3(esk2_0,k2_relat_1(esk2_0),X1) = esk1_0
    | ~ r2_hidden(X1,k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X30,X31] :
      ( ~ m1_subset_1(X30,X31)
      | v1_xboole_0(X31)
      | r2_hidden(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk2_0))
    | ~ r2_hidden(X1,k1_tarski(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk2_0,esk1_0) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_16]),c_0_17])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X26] : m1_subset_1(esk7_1(X26),X26) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_34,negated_conjecture,
    ( k1_funct_1(esk2_0,esk1_0) = X1
    | ~ m1_subset_1(X1,k2_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk2_0,esk1_0) = esk7_1(k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,negated_conjecture,
    ( esk7_1(k2_relat_1(esk2_0)) = X1
    | ~ r2_hidden(X1,k2_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_30,c_0_36])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,negated_conjecture,
    ( k2_relat_1(esk2_0) != k1_tarski(k1_funct_1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( esk3_2(X1,k2_relat_1(esk2_0)) = esk7_1(k2_relat_1(esk2_0))
    | esk3_2(X1,k2_relat_1(esk2_0)) = X1
    | k1_tarski(X1) = k2_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( k1_tarski(esk7_1(k2_relat_1(esk2_0))) != k2_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_39,c_0_36])).

cnf(c_0_42,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( esk3_2(esk7_1(k2_relat_1(esk2_0)),k2_relat_1(esk2_0)) = esk7_1(k2_relat_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_40])]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk7_1(k2_relat_1(esk2_0)),k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_36]),c_0_15]),c_0_29]),c_0_16]),c_0_17])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
