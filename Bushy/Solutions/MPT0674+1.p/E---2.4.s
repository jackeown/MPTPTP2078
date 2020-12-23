%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_1__t117_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:13 EDT 2019

% Result     : Theorem 265.13s
% Output     : CNFRefutation 265.13s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 193 expanded)
%              Number of clauses        :   35 (  93 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 791 expanded)
%              Number of equality atoms :   70 ( 297 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t117_funct_1.p',t117_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t117_funct_1.p',d1_tarski)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t117_funct_1.p',d12_funct_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t117_funct_1.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t117_funct_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t117_funct_1.p',existence_m1_subset_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t117_funct_1.p',d16_relat_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

fof(c_0_8,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X24
        | X25 != k1_tarski(X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k1_tarski(X24) )
      & ( ~ r2_hidden(esk6_2(X28,X29),X29)
        | esk6_2(X28,X29) != X28
        | X29 = k1_tarski(X28) )
      & ( r2_hidden(esk6_2(X28,X29),X29)
        | esk6_2(X28,X29) = X28
        | X29 = k1_tarski(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(esk3_4(X10,X11,X12,X13),k1_relat_1(X10))
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk3_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X13 = k1_funct_1(X10,esk3_4(X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X16,k1_relat_1(X10))
        | ~ r2_hidden(X16,X11)
        | X15 != k1_funct_1(X10,X16)
        | r2_hidden(X15,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk4_3(X10,X17,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X10))
        | ~ r2_hidden(X20,X17)
        | esk4_3(X10,X17,X18) != k1_funct_1(X10,X20)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk5_3(X10,X17,X18),k1_relat_1(X10))
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk5_3(X10,X17,X18),X17)
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk4_3(X10,X17,X18) = k1_funct_1(X10,esk5_3(X10,X17,X18))
        | r2_hidden(esk4_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r2_hidden(esk1_0,k1_relat_1(esk2_0))
    & k11_relat_1(esk2_0,esk1_0) != k1_tarski(k1_funct_1(esk2_0,esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_11,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X2)
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | X2 != k1_tarski(X1) ),
    inference(er,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X35,X36] :
      ( ~ m1_subset_1(X35,X36)
      | v1_xboole_0(X36)
      | r2_hidden(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_20,plain,(
    ! [X31] : m1_subset_1(esk7_1(X31),X31) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_21,plain,
    ( X3 = k9_relat_1(X1,X2)
    | ~ r2_hidden(esk4_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,k1_relat_1(X1))
    | ~ r2_hidden(X4,X2)
    | esk4_3(X1,X2,X3) != k1_funct_1(X1,X4)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( esk4_3(X1,X2,X3) = k1_funct_1(X1,esk5_3(X1,X2,X3))
    | r2_hidden(esk4_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,X2)
    | r2_hidden(esk4_3(esk2_0,X2,X1),X1)
    | r2_hidden(esk5_3(esk2_0,X2,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_26,plain,
    ( X1 != k1_tarski(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk7_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,X2)
    | esk4_3(esk2_0,X2,X1) != k1_funct_1(esk2_0,esk1_0)
    | ~ r2_hidden(esk4_3(esk2_0,X2,X1),X1)
    | ~ r2_hidden(esk1_0,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15]),c_0_16])])).

cnf(c_0_30,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_3(esk2_0,X1,X2)) = esk4_3(esk2_0,X1,X2)
    | X2 = k9_relat_1(esk2_0,X1)
    | r2_hidden(esk4_3(esk2_0,X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_15]),c_0_16])])).

cnf(c_0_31,negated_conjecture,
    ( esk5_3(esk2_0,k1_tarski(X1),X2) = X1
    | X2 = k9_relat_1(esk2_0,k1_tarski(X1))
    | r2_hidden(esk4_3(esk2_0,k1_tarski(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk7_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | k11_relat_1(X22,X23) = k9_relat_1(X22,k1_tarski(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_35,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,X2)
    | esk4_3(esk2_0,X2,X1) != k1_funct_1(esk2_0,esk1_0)
    | X2 != k1_tarski(esk1_0)
    | ~ r2_hidden(esk4_3(esk2_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_18])).

cnf(c_0_36,negated_conjecture,
    ( k1_funct_1(esk2_0,esk5_3(esk2_0,X1,k1_tarski(X2))) = esk4_3(esk2_0,X1,k1_tarski(X2))
    | esk4_3(esk2_0,X1,k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( esk5_3(esk2_0,k1_tarski(X1),k1_tarski(X2)) = X1
    | esk4_3(esk2_0,k1_tarski(X1),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk2_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(esk7_1(k1_tarski(X1)),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( X1 = k9_relat_1(esk2_0,k1_tarski(esk1_0))
    | esk4_3(esk2_0,k1_tarski(esk1_0),X1) != k1_funct_1(esk2_0,esk1_0)
    | ~ r2_hidden(esk4_3(esk2_0,k1_tarski(esk1_0),X1),X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( esk4_3(esk2_0,k1_tarski(X1),k1_tarski(X2)) = k1_funct_1(esk2_0,X1)
    | esk4_3(esk2_0,k1_tarski(X1),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk2_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( esk7_1(k1_tarski(X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_24,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k11_relat_1(esk2_0,esk1_0) != k1_tarski(k1_funct_1(esk2_0,esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( k11_relat_1(esk2_0,X1) = k9_relat_1(esk2_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( esk4_3(esk2_0,k1_tarski(esk1_0),k1_tarski(X1)) = X1
    | k1_tarski(X1) = k9_relat_1(esk2_0,k1_tarski(esk1_0))
    | ~ r2_hidden(k1_funct_1(esk2_0,esk1_0),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(rw,[status(thm)],[c_0_38,c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk2_0,esk1_0)) != k9_relat_1(esk2_0,k1_tarski(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( esk4_3(esk2_0,k1_tarski(esk1_0),k1_tarski(k1_funct_1(esk2_0,esk1_0))) = k1_funct_1(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_48]),c_0_46])]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
