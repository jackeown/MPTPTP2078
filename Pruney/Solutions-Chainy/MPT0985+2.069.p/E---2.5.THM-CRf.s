%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 728 expanded)
%              Number of clauses        :   60 ( 287 expanded)
%              Number of leaves         :   15 ( 187 expanded)
%              Depth                    :   17
%              Number of atoms          :  291 (3385 expanded)
%              Number of equality atoms :  100 ( 719 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X3)
            & k2_relset_1(X1,X2,X3) = X2 )
         => ( v1_funct_1(k2_funct_1(X3))
            & v1_funct_2(k2_funct_1(X3),X2,X1)
            & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_funct_2])).

fof(c_0_16,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk6_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
    & v2_funct_1(esk7_0)
    & k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0
    & ( ~ v1_funct_1(k2_funct_1(esk7_0))
      | ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
      | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X40] :
      ( ( v1_funct_1(X40)
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( v1_funct_2(X40,k1_relat_1(X40),k2_relat_1(X40))
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) )
      & ( m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X40),k2_relat_1(X40))))
        | ~ v1_relat_1(X40)
        | ~ v1_funct_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_19,plain,(
    ! [X27] :
      ( ( k2_relat_1(X27) = k1_relat_1(k2_funct_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( k1_relat_1(X27) = k2_relat_1(k2_funct_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_20,plain,(
    ! [X26] :
      ( ( v1_relat_1(k2_funct_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( v1_funct_1(k2_funct_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_21,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_relset_1(X34,X35,X36) = k2_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_24,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_25,plain,(
    ! [X15,X16,X17,X19,X20,X21,X22,X24] :
      ( ( ~ r2_hidden(X17,X16)
        | r2_hidden(k4_tarski(esk2_3(X15,X16,X17),X17),X15)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X19),X15)
        | r2_hidden(X19,X16)
        | X16 != k2_relat_1(X15) )
      & ( ~ r2_hidden(esk3_2(X21,X22),X22)
        | ~ r2_hidden(k4_tarski(X24,esk3_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) )
      & ( r2_hidden(esk3_2(X21,X22),X22)
        | r2_hidden(k4_tarski(esk4_2(X21,X22),esk3_2(X21,X22)),X21)
        | X22 = k2_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k2_relset_1(esk5_0,esk6_0,esk7_0) = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_36,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk7_0)) = k1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(esk7_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_22])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_44,plain,(
    ! [X37,X38,X39] :
      ( ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X39 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != k1_xboole_0
        | v1_funct_2(X39,X37,X38)
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_45,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_46,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk3_2(X2,X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_48,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_relat_1(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_31]),c_0_32]),c_0_33])])).

fof(c_0_50,plain,(
    ! [X9,X10] :
      ( ~ v1_xboole_0(X9)
      | X9 = X10
      | ~ v1_xboole_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk7_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk6_0,k1_relat_1(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_49])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_47])])).

cnf(c_0_60,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk7_0))
    | esk6_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_47])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( X1 = esk7_0
    | esk6_0 != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_57])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( k2_funct_1(esk7_0) = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)
    | ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

cnf(c_0_71,negated_conjecture,
    ( k2_funct_1(esk7_0) = esk7_0
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))
    | esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_52])).

cnf(c_0_73,plain,
    ( v1_funct_2(X1,X2,X3)
    | k2_relat_1(X1) != k1_xboole_0
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k1_relat_1(esk7_0) = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_67]),c_0_48])).

cnf(c_0_75,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_76,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_22]),c_0_69])])).

cnf(c_0_77,negated_conjecture,
    ( esk6_0 != k1_xboole_0
    | ~ v1_funct_2(esk7_0,esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_32])]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk7_0,X1,X2)
    | esk6_0 != k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_41]),c_0_32]),c_0_33])])).

cnf(c_0_79,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_80,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_76]),c_0_22])])).

cnf(c_0_81,negated_conjecture,
    ( esk6_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk7_0),esk6_0,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_40]),c_0_41]),c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_83,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(sr,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0))
    | ~ m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_84])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_29]),c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:21:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.19/0.40  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.029 s
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.40  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.40  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.40  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.19/0.40  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.40  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.40  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.19/0.40  fof(c_0_16, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.40  fof(c_0_17, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((v2_funct_1(esk7_0)&k2_relset_1(esk5_0,esk6_0,esk7_0)=esk6_0)&(~v1_funct_1(k2_funct_1(esk7_0))|~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.40  fof(c_0_18, plain, ![X40]:(((v1_funct_1(X40)|(~v1_relat_1(X40)|~v1_funct_1(X40)))&(v1_funct_2(X40,k1_relat_1(X40),k2_relat_1(X40))|(~v1_relat_1(X40)|~v1_funct_1(X40))))&(m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X40),k2_relat_1(X40))))|(~v1_relat_1(X40)|~v1_funct_1(X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.40  fof(c_0_19, plain, ![X27]:((k2_relat_1(X27)=k1_relat_1(k2_funct_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(k1_relat_1(X27)=k2_relat_1(k2_funct_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.40  fof(c_0_20, plain, ![X26]:((v1_relat_1(k2_funct_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(v1_funct_1(k2_funct_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.40  cnf(c_0_21, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  fof(c_0_23, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_relset_1(X34,X35,X36)=k2_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.40  fof(c_0_24, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.40  fof(c_0_25, plain, ![X15, X16, X17, X19, X20, X21, X22, X24]:(((~r2_hidden(X17,X16)|r2_hidden(k4_tarski(esk2_3(X15,X16,X17),X17),X15)|X16!=k2_relat_1(X15))&(~r2_hidden(k4_tarski(X20,X19),X15)|r2_hidden(X19,X16)|X16!=k2_relat_1(X15)))&((~r2_hidden(esk3_2(X21,X22),X22)|~r2_hidden(k4_tarski(X24,esk3_2(X21,X22)),X21)|X22=k2_relat_1(X21))&(r2_hidden(esk3_2(X21,X22),X22)|r2_hidden(k4_tarski(esk4_2(X21,X22),esk3_2(X21,X22)),X21)|X22=k2_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.19/0.40  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_27, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_28, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_29, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.40  cnf(c_0_30, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.40  cnf(c_0_31, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.40  cnf(c_0_34, negated_conjecture, (k2_relset_1(esk5_0,esk6_0,esk7_0)=esk6_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_35, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.40  fof(c_0_36, plain, ![X13, X14]:(~v1_xboole_0(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.40  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.40  cnf(c_0_38, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.40  cnf(c_0_39, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.40  cnf(c_0_40, negated_conjecture, (k2_relat_1(k2_funct_1(esk7_0))=k1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])])).
% 0.19/0.40  cnf(c_0_41, negated_conjecture, (k2_relat_1(esk7_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_22])])).
% 0.19/0.40  cnf(c_0_42, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.40  fof(c_0_43, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.40  fof(c_0_44, plain, ![X37, X38, X39]:((((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))&((~v1_funct_2(X39,X37,X38)|X39=k1_xboole_0|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X39!=k1_xboole_0|v1_funct_2(X39,X37,X38)|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.40  fof(c_0_45, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.40  cnf(c_0_46, plain, (X1=k2_relat_1(X2)|r2_hidden(esk3_2(X2,X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.40  cnf(c_0_47, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.40  cnf(c_0_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_relat_1(esk7_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_31]), c_0_32]), c_0_33])])).
% 0.19/0.40  fof(c_0_50, plain, ![X9, X10]:(~v1_xboole_0(X9)|X9=X10|~v1_xboole_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.40  cnf(c_0_51, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_42, c_0_22])).
% 0.19/0.40  cnf(c_0_52, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_53, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.40  cnf(c_0_54, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.40  cnf(c_0_55, plain, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.19/0.40  cnf(c_0_56, negated_conjecture, (v1_xboole_0(k2_funct_1(esk7_0))|~v1_xboole_0(k2_zfmisc_1(esk6_0,k1_relat_1(esk7_0)))), inference(spm,[status(thm)],[c_0_42, c_0_49])).
% 0.19/0.40  cnf(c_0_57, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.40  cnf(c_0_58, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.40  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk7_0)|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_47])])).
% 0.19/0.40  cnf(c_0_60, plain, (v1_funct_2(X1,X2,X3)|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.40  cnf(c_0_61, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_37, c_0_55])).
% 0.19/0.40  cnf(c_0_62, negated_conjecture, (v1_xboole_0(k2_funct_1(esk7_0))|esk6_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_47])])).
% 0.19/0.40  cnf(c_0_63, negated_conjecture, (~v1_funct_1(k2_funct_1(esk7_0))|~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_64, negated_conjecture, (X1=esk7_0|esk6_0!=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.40  cnf(c_0_65, plain, (v1_funct_2(X1,X2,X3)|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_60, c_0_57])).
% 0.19/0.40  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|k2_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_52])).
% 0.19/0.40  cnf(c_0_67, negated_conjecture, (k2_funct_1(esk7_0)=k1_xboole_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.40  cnf(c_0_68, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.40  cnf(c_0_69, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.40  cnf(c_0_70, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)|~v1_funct_1(k2_funct_1(esk7_0))|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_63, c_0_57])).
% 0.19/0.40  cnf(c_0_71, negated_conjecture, (k2_funct_1(esk7_0)=esk7_0|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_62])).
% 0.19/0.40  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k1_xboole_0))|esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_52])).
% 0.19/0.40  cnf(c_0_73, plain, (v1_funct_2(X1,X2,X3)|k2_relat_1(X1)!=k1_xboole_0|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.40  cnf(c_0_74, negated_conjecture, (k1_relat_1(esk7_0)=k1_xboole_0|esk6_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_67]), c_0_48])).
% 0.19/0.40  cnf(c_0_75, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.40  cnf(c_0_76, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_22]), c_0_69])])).
% 0.19/0.40  cnf(c_0_77, negated_conjecture, (esk6_0!=k1_xboole_0|~v1_funct_2(esk7_0,esk6_0,esk5_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_32])]), c_0_72])).
% 0.19/0.40  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk7_0,X1,X2)|esk6_0!=k1_xboole_0|k1_xboole_0!=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_41]), c_0_32]), c_0_33])])).
% 0.19/0.40  cnf(c_0_79, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_27]), c_0_28]), c_0_29])).
% 0.19/0.40  cnf(c_0_80, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_76]), c_0_22])])).
% 0.19/0.40  cnf(c_0_81, negated_conjecture, (esk6_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.40  cnf(c_0_82, negated_conjecture, (v1_funct_2(k2_funct_1(esk7_0),esk6_0,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_40]), c_0_41]), c_0_31]), c_0_32]), c_0_33])])).
% 0.19/0.40  cnf(c_0_83, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(sr,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.40  cnf(c_0_84, negated_conjecture, (v1_funct_2(k2_funct_1(esk7_0),esk6_0,esk5_0)), inference(rw,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.40  cnf(c_0_85, negated_conjecture, (~v1_funct_1(k2_funct_1(esk7_0))|~m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_84])])).
% 0.19/0.40  cnf(c_0_86, negated_conjecture, (m1_subset_1(k2_funct_1(esk7_0),k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk5_0)))), inference(rw,[status(thm)],[c_0_49, c_0_83])).
% 0.19/0.40  cnf(c_0_87, negated_conjecture, (~v1_funct_1(k2_funct_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 0.19/0.40  cnf(c_0_88, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_29]), c_0_32]), c_0_33])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 89
% 0.19/0.40  # Proof object clause steps            : 60
% 0.19/0.40  # Proof object formula steps           : 29
% 0.19/0.40  # Proof object conjectures             : 35
% 0.19/0.40  # Proof object clause conjectures      : 32
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 25
% 0.19/0.40  # Proof object initial formulas used   : 15
% 0.19/0.40  # Proof object generating inferences   : 30
% 0.19/0.40  # Proof object simplifying inferences  : 47
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 15
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 36
% 0.19/0.40  # Removed in clause preprocessing      : 1
% 0.19/0.40  # Initial clauses in saturation        : 35
% 0.19/0.40  # Processed clauses                    : 457
% 0.19/0.40  # ...of these trivial                  : 12
% 0.19/0.40  # ...subsumed                          : 189
% 0.19/0.40  # ...remaining for further processing  : 256
% 0.19/0.40  # Other redundant clauses eliminated   : 8
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 11
% 0.19/0.40  # Backward-rewritten                   : 29
% 0.19/0.40  # Generated clauses                    : 1448
% 0.19/0.40  # ...of the previous two non-trivial   : 1271
% 0.19/0.40  # Contextual simplify-reflections      : 28
% 0.19/0.40  # Paramodulations                      : 1390
% 0.19/0.40  # Factorizations                       : 34
% 0.19/0.40  # Equation resolutions                 : 21
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 213
% 0.19/0.40  #    Positive orientable unit clauses  : 14
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 5
% 0.19/0.40  #    Non-unit-clauses                  : 194
% 0.19/0.40  # Current number of unprocessed clauses: 835
% 0.19/0.40  # ...number of literals in the above   : 2962
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 43
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 2988
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 1690
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 174
% 0.19/0.40  # Unit Clause-clause subsumption calls : 215
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 9
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 17641
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.063 s
% 0.19/0.40  # System time              : 0.006 s
% 0.19/0.40  # Total time               : 0.070 s
% 0.19/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
