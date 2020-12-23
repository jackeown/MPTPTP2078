%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : relset_1__t23_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:08 EDT 2019

% Result     : Theorem 151.72s
% Output     : CNFRefutation 151.72s
% Verified   : 
% Statistics : Number of formulae       :   79 (4357 expanded)
%              Number of clauses        :   53 (2224 expanded)
%              Number of leaves         :   13 (1100 expanded)
%              Depth                    :   22
%              Number of atoms          :  195 (11881 expanded)
%              Number of equality atoms :   54 (2931 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t6_boole)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',d5_relat_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',dt_o_0_0_xboole_0)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t7_boole)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t2_subset)).

fof(t23_relset_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t23_relset_1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',dt_k2_relset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',existence_m1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t5_subset)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t2_tarski)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',redefinition_k2_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t4_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t23_relset_1.p',t1_subset)).

fof(c_0_13,plain,(
    ! [X52] :
      ( ~ v1_xboole_0(X52)
      | X52 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_14,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(esk6_3(X15,X16,X17),X17),X15)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(esk7_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk7_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) )
      & ( r2_hidden(esk7_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk8_2(X21,X22),esk7_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_17,plain,(
    ! [X53,X54] :
      ( ~ r2_hidden(X53,X54)
      | ~ v1_xboole_0(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_18,plain,
    ( r2_hidden(k4_tarski(esk6_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,plain,(
    ! [X39,X40] :
      ( ~ m1_subset_1(X39,X40)
      | v1_xboole_0(X40)
      | r2_hidden(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
        <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t23_relset_1])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(esk6_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_19])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | m1_subset_1(k2_relset_1(X26,X27,X28),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_27,negated_conjecture,(
    ! [X10,X11] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
      & ( r2_hidden(esk4_0,esk2_0)
        | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 )
      & ( ~ r2_hidden(k4_tarski(X10,esk4_0),esk3_0)
        | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 )
      & ( ~ r2_hidden(X11,esk2_0)
        | r2_hidden(k4_tarski(esk5_1(X11),X11),esk3_0)
        | k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])])])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X29] : m1_subset_1(esk9_1(X29),X29) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_31,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | ~ v1_xboole_0(X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_32,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_relat_1(X1) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k2_relset_1(esk1_0,esk2_0,esk3_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k2_relat_1(X1) = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    | ~ r2_hidden(X1,k2_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_relat_1(k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_41,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_16])).

fof(c_0_42,plain,(
    ! [X41,X42] :
      ( ( ~ r2_hidden(esk10_2(X41,X42),X41)
        | ~ r2_hidden(esk10_2(X41,X42),X42)
        | X41 = X42 )
      & ( r2_hidden(esk10_2(X41,X42),X41)
        | r2_hidden(esk10_2(X41,X42),X42)
        | X41 = X42 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X2,k2_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_25])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,o_0_0_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16]),c_0_41])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r2_hidden(esk10_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk9_1(esk2_0),esk2_0)
    | ~ r2_hidden(X1,k2_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_35])).

cnf(c_0_47,plain,
    ( o_0_0_xboole_0 = X1
    | r2_hidden(esk10_2(o_0_0_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | r2_hidden(esk9_1(esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_49,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_relset_1(X31,X32,X33) = k2_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_50,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_48])).

cnf(c_0_51,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_52,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_53,plain,(
    ! [X46,X47,X48] :
      ( ~ r2_hidden(X46,X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(X48))
      | m1_subset_1(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ r2_hidden(esk10_2(X1,X2),X1)
    | ~ r2_hidden(esk10_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_1(X1),X1),esk3_0)
    | k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(esk3_0) = k2_relset_1(esk1_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_33])).

fof(c_0_59,plain,(
    ! [X34,X35] :
      ( ~ r2_hidden(X34,X35)
      | m1_subset_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | X1 = esk2_0
    | ~ r2_hidden(esk10_2(X1,esk2_0),X1)
    | ~ m1_subset_1(esk10_2(X1,esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    | r2_hidden(X1,k2_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(X1,esk2_0)
    | ~ r2_hidden(X1,k2_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_37])).

cnf(c_0_65,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    | k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | ~ r2_hidden(esk10_2(k2_relset_1(esk1_0,esk2_0,esk3_0),esk2_0),esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk4_0),esk3_0)
    | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = X1
    | r2_hidden(esk10_2(k2_relset_1(esk1_0,esk2_0,esk3_0),X1),X1)
    | m1_subset_1(esk10_2(k2_relset_1(esk1_0,esk2_0,esk3_0),X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_45])).

cnf(c_0_68,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    | ~ m1_subset_1(esk10_2(k2_relset_1(esk1_0,esk2_0,esk3_0),esk2_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0
    | ~ r2_hidden(esk4_0,k2_relset_1(esk1_0,esk2_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_23]),c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_67]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0
    | ~ r2_hidden(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | k2_relset_1(esk1_0,esk2_0,esk3_0) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_73,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    | ~ v1_xboole_0(k2_relset_1(esk1_0,esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = o_0_0_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_74]),c_0_16])])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(esk4_0,esk2_0)
    | esk2_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77]),c_0_77])]),c_0_44]),
    [proof]).
%------------------------------------------------------------------------------
