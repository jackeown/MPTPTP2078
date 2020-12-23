%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relat_1__t23_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:00 EDT 2019

% Result     : Theorem 38.42s
% Output     : CNFRefutation 38.42s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 343 expanded)
%              Number of clauses        :   44 ( 169 expanded)
%              Number of leaves         :    9 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  171 (1154 expanded)
%              Number of equality atoms :   82 ( 646 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',d1_tarski)).

fof(t23_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',t23_relat_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',existence_m1_subset_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',d4_relat_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',t33_zfmisc_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',t2_tarski)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t23_relat_1.p',d5_relat_1)).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk4_2(X14,X15),X15)
        | esk4_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk4_2(X14,X15),X15)
        | esk4_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( X3 = k1_tarski(k4_tarski(X1,X2))
         => ( k1_relat_1(X3) = k1_tarski(X1)
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_relat_1])).

fof(c_0_11,plain,(
    ! [X53,X54] :
      ( ~ r2_hidden(X53,X54)
      | ~ v1_xboole_0(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & esk3_0 = k1_tarski(k4_tarski(esk1_0,esk2_0))
    & ( k1_relat_1(esk3_0) != k1_tarski(esk1_0)
      | k2_relat_1(esk3_0) != k1_tarski(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])])).

cnf(c_0_17,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = k1_tarski(k4_tarski(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,X44)
      | v1_xboole_0(X44)
      | r2_hidden(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( X1 = k4_tarski(esk1_0,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

fof(c_0_24,plain,(
    ! [X39] : m1_subset_1(esk11_1(X39),X39) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_25,plain,(
    ! [X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( ~ r2_hidden(X19,X18)
        | r2_hidden(k4_tarski(X19,esk5_3(X17,X18,X19)),X17)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X21,X22),X17)
        | r2_hidden(X21,X18)
        | X18 != k1_relat_1(X17) )
      & ( ~ r2_hidden(esk6_2(X23,X24),X24)
        | ~ r2_hidden(k4_tarski(esk6_2(X23,X24),X26),X23)
        | X24 = k1_relat_1(X23) )
      & ( r2_hidden(esk6_2(X23,X24),X24)
        | r2_hidden(k4_tarski(esk6_2(X23,X24),esk7_2(X23,X24)),X23)
        | X24 = k1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_26,plain,(
    ! [X48,X49,X50,X51] :
      ( ( X48 = X50
        | k4_tarski(X48,X49) != k4_tarski(X50,X51) )
      & ( X49 = X51
        | k4_tarski(X48,X49) != k4_tarski(X50,X51) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_27,negated_conjecture,
    ( X1 = k4_tarski(esk1_0,esk2_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk11_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X1,esk5_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( k4_tarski(esk1_0,esk2_0) = esk11_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X1,esk5_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_33,plain,(
    ! [X45,X46] :
      ( ( ~ r2_hidden(esk12_2(X45,X46),X45)
        | ~ r2_hidden(esk12_2(X45,X46),X46)
        | X45 = X46 )
      & ( r2_hidden(esk12_2(X45,X46),X45)
        | r2_hidden(esk12_2(X45,X46),X46)
        | X45 = X46 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

fof(c_0_34,plain,(
    ! [X28,X29,X30,X32,X33,X34,X35,X37] :
      ( ( ~ r2_hidden(X30,X29)
        | r2_hidden(k4_tarski(esk8_3(X28,X29,X30),X30),X28)
        | X29 != k2_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X33,X32),X28)
        | r2_hidden(X32,X29)
        | X29 != k2_relat_1(X28) )
      & ( ~ r2_hidden(esk9_2(X34,X35),X35)
        | ~ r2_hidden(k4_tarski(X37,esk9_2(X34,X35)),X34)
        | X35 = k2_relat_1(X34) )
      & ( r2_hidden(esk9_2(X34,X35),X35)
        | r2_hidden(k4_tarski(esk10_2(X34,X35),esk9_2(X34,X35)),X34)
        | X35 = k2_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( esk1_0 = X1
    | k4_tarski(X1,X2) != esk11_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,plain,
    ( k4_tarski(X1,esk5_3(k1_tarski(X2),k1_relat_1(k1_tarski(X2)),X1)) = X2
    | ~ r2_hidden(X1,k1_relat_1(k1_tarski(X2))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k1_tarski(esk11_1(esk3_0)) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(esk12_2(X1,X2),X1)
    | r2_hidden(esk12_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( r2_hidden(k4_tarski(esk8_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( esk1_0 = X1
    | ~ r2_hidden(X1,k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36])]),c_0_37])).

cnf(c_0_41,plain,
    ( esk12_2(k1_tarski(X1),X2) = X1
    | k1_tarski(X1) = X2
    | r2_hidden(esk12_2(k1_tarski(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_43,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_tarski(esk8_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( esk12_2(k1_tarski(X1),k1_relat_1(esk3_0)) = esk1_0
    | esk12_2(k1_tarski(X1),k1_relat_1(esk3_0)) = X1
    | k1_tarski(X1) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_0,esk2_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = X1
    | k4_tarski(X2,X1) != esk11_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_31])).

cnf(c_0_49,plain,
    ( k4_tarski(esk8_3(k1_tarski(X1),k2_relat_1(k1_tarski(X1)),X2),X2) = X1
    | ~ r2_hidden(X2,k2_relat_1(k1_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_44])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r2_hidden(esk12_2(X1,X2),X1)
    | ~ r2_hidden(esk12_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_51,negated_conjecture,
    ( esk12_2(k1_tarski(esk1_0),k1_relat_1(esk3_0)) = esk1_0
    | k1_relat_1(esk3_0) = k1_tarski(esk1_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_45])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( esk2_0 = X1
    | ~ r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49])]),c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(esk3_0) != k1_tarski(esk1_0)
    | k2_relat_1(esk3_0) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_tarski(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_16])])).

cnf(c_0_56,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( esk12_2(k1_tarski(X1),k2_relat_1(esk3_0)) = esk2_0
    | esk12_2(k1_tarski(X1),k2_relat_1(esk3_0)) = X1
    | k1_tarski(X1) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( k1_tarski(esk2_0) != k2_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( esk12_2(k1_tarski(esk2_0),k2_relat_1(esk3_0)) = esk2_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_57])]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk2_0,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_60]),c_0_61]),c_0_16])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
