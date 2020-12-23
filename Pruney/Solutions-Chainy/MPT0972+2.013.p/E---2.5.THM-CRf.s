%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:44 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   88 (1058 expanded)
%              Number of clauses        :   62 ( 454 expanded)
%              Number of leaves         :   13 ( 264 expanded)
%              Depth                    :   14
%              Number of atoms          :  282 (5130 expanded)
%              Number of equality atoms :   90 (1048 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(rc1_subset_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( r2_hidden(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_2])).

fof(c_0_14,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X40 = k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X39 = k1_relset_1(X39,X40,X41)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_relset_1(X39,X40,X41)
        | v1_funct_2(X41,X39,X40)
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( ~ v1_funct_2(X41,X39,X40)
        | X41 = k1_xboole_0
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X41 != k1_xboole_0
        | v1_funct_2(X41,X39,X40)
        | X39 = k1_xboole_0
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_15,negated_conjecture,(
    ! [X46] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & ( ~ r2_hidden(X46,esk5_0)
        | k1_funct_1(esk7_0,X46) = k1_funct_1(esk8_0,X46) )
      & ~ r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_17,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_19,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | ~ r2_hidden(X20,X19)
      | r2_hidden(X20,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_20,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X23,X24] :
      ( ( r2_hidden(esk4_2(X23,X24),k1_relat_1(X23))
        | k1_relat_1(X23) != k1_relat_1(X24)
        | X23 = X24
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( k1_funct_1(X23,esk4_2(X23,X24)) != k1_funct_1(X24,esk4_2(X23,X24))
        | k1_relat_1(X23) != k1_relat_1(X24)
        | X23 = X24
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_30,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_32,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_38,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_33]),c_0_34])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_33])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_45,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_xboole_0(X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29)))
      | v1_xboole_0(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_46,plain,(
    ! [X21] :
      ( ( m1_subset_1(esk3_1(X21),k1_zfmisc_1(X21))
        | v1_xboole_0(X21) )
      & ( ~ v1_xboole_0(esk3_1(X21))
        | v1_xboole_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_33])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | r2_hidden(esk2_2(esk8_0,X1),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_50,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk8_0 = X1
    | r2_hidden(esk4_2(esk8_0,X1),esk5_0)
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_54,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_36])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(esk3_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(esk7_0,X1)
    | r2_hidden(esk2_2(esk7_0,X1),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_61,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk4_2(X1,X2)) != k1_funct_1(X2,esk4_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_funct_1(esk8_0,X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk4_2(esk8_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_64,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

fof(c_0_66,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ r2_relset_1(X35,X36,X37,X38)
        | X37 = X38
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != X38
        | r2_relset_1(X35,X36,X37,X38)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = esk8_0
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk8_0 = X1
    | k1_funct_1(esk8_0,esk4_2(esk8_0,X1)) != k1_funct_1(X1,esk4_2(esk8_0,X1))
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(esk8_0,esk4_2(esk8_0,esk7_0)) = k1_funct_1(esk7_0,esk4_2(esk8_0,esk7_0))
    | esk6_0 = k1_xboole_0
    | esk8_0 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = esk7_0
    | ~ r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = esk8_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_52]),c_0_53])]),c_0_70])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_55])).

cnf(c_0_77,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( k2_zfmisc_1(esk5_0,esk6_0) = esk7_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_36])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_80,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_76]),c_0_55])])).

cnf(c_0_81,negated_conjecture,
    ( r2_relset_1(esk5_0,esk6_0,esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_33])).

cnf(c_0_82,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_75]),c_0_76]),c_0_76]),c_0_55])])).

cnf(c_0_83,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_84,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk6_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_83]),c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_85]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.13/0.39  # and selection function SelectNewComplexAHPNS.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t18_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 0.13/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.13/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.13/0.39  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.13/0.39  fof(rc1_subset_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&~(v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_subset_1)).
% 0.13/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.39  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.13/0.39  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t18_funct_2])).
% 0.13/0.39  fof(c_0_14, plain, ![X39, X40, X41]:((((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X40=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&((~v1_funct_2(X41,X39,X40)|X39=k1_relset_1(X39,X40,X41)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X39!=k1_relset_1(X39,X40,X41)|v1_funct_2(X41,X39,X40)|X39!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))))&((~v1_funct_2(X41,X39,X40)|X41=k1_xboole_0|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))&(X41!=k1_xboole_0|v1_funct_2(X41,X39,X40)|X39=k1_xboole_0|X40!=k1_xboole_0|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.39  fof(c_0_15, negated_conjecture, ![X46]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((~r2_hidden(X46,esk5_0)|k1_funct_1(esk7_0,X46)=k1_funct_1(esk8_0,X46))&~r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.13/0.39  fof(c_0_16, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.39  fof(c_0_17, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.39  fof(c_0_18, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  fof(c_0_19, plain, ![X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(X18))|(~r2_hidden(X20,X19)|r2_hidden(X20,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.13/0.39  cnf(c_0_20, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_23, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_24, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.39  fof(c_0_25, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  cnf(c_0_26, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_27, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_28, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  fof(c_0_29, plain, ![X23, X24]:((r2_hidden(esk4_2(X23,X24),k1_relat_1(X23))|k1_relat_1(X23)!=k1_relat_1(X24)|X23=X24|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(k1_funct_1(X23,esk4_2(X23,X24))!=k1_funct_1(X24,esk4_2(X23,X24))|k1_relat_1(X23)!=k1_relat_1(X24)|X23=X24|(~v1_relat_1(X24)|~v1_funct_1(X24))|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.13/0.39  cnf(c_0_32, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.39  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 0.13/0.39  cnf(c_0_38, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_21])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_33]), c_0_34])])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_23, c_0_33])).
% 0.13/0.39  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.39  fof(c_0_45, plain, ![X29, X30, X31]:(~v1_xboole_0(X29)|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X30,X29)))|v1_xboole_0(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.13/0.39  fof(c_0_46, plain, ![X21]:((m1_subset_1(esk3_1(X21),k1_zfmisc_1(X21))|v1_xboole_0(X21))&(~v1_xboole_0(esk3_1(X21))|v1_xboole_0(X21))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc1_subset_1])])])])])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_28, c_0_33])).
% 0.13/0.39  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (r1_tarski(esk8_0,X1)|r2_hidden(esk2_2(esk8_0,X1),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (esk6_0=k1_xboole_0|esk8_0=X1|r2_hidden(esk4_2(esk8_0,X1),esk5_0)|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.39  cnf(c_0_54, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_44, c_0_36])).
% 0.13/0.39  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.39  cnf(c_0_56, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.39  cnf(c_0_57, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(X1))|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_58, plain, (v1_xboole_0(X1)|~v1_xboole_0(esk3_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (r1_tarski(esk7_0,X1)|r2_hidden(esk2_2(esk7_0,X1),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_27])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.13/0.39  cnf(c_0_61, plain, (X1=X2|k1_funct_1(X1,esk4_2(X1,X2))!=k1_funct_1(X2,esk4_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_funct_1(esk8_0,X1)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (esk8_0=esk7_0|esk6_0=k1_xboole_0|r2_hidden(esk4_2(esk8_0,esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 0.13/0.39  cnf(c_0_64, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.39  cnf(c_0_65, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.13/0.39  fof(c_0_66, plain, ![X35, X36, X37, X38]:((~r2_relset_1(X35,X36,X37,X38)|X37=X38|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(X37!=X38|r2_relset_1(X35,X36,X37,X38)|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_48, c_0_59])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=esk8_0|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_60])).
% 0.13/0.39  cnf(c_0_69, negated_conjecture, (esk6_0=k1_xboole_0|esk8_0=X1|k1_funct_1(esk8_0,esk4_2(esk8_0,X1))!=k1_funct_1(X1,esk4_2(esk8_0,X1))|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_39]), c_0_40]), c_0_41])])).
% 0.13/0.39  cnf(c_0_70, negated_conjecture, (k1_funct_1(esk8_0,esk4_2(esk8_0,esk7_0))=k1_funct_1(esk7_0,esk4_2(esk8_0,esk7_0))|esk6_0=k1_xboole_0|esk8_0=esk7_0), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.39  cnf(c_0_71, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.39  cnf(c_0_72, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=esk7_0|~r1_tarski(k2_zfmisc_1(esk5_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_35, c_0_67])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=esk8_0|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_68, c_0_36])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (esk8_0=esk7_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_51]), c_0_52]), c_0_53])]), c_0_70])).
% 0.13/0.39  cnf(c_0_76, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_55])).
% 0.13/0.39  cnf(c_0_77, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_72])).
% 0.13/0.39  cnf(c_0_78, negated_conjecture, (k2_zfmisc_1(esk5_0,esk6_0)=esk7_0|~v1_xboole_0(k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_73, c_0_36])).
% 0.13/0.39  cnf(c_0_79, negated_conjecture, (~r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (esk8_0=esk7_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_76]), c_0_55])])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (r2_relset_1(esk5_0,esk6_0,esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_77, c_0_33])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (esk8_0=esk7_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_75]), c_0_76]), c_0_76]), c_0_55])])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.13/0.39  cnf(c_0_85, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(rw,[status(thm)],[c_0_21, c_0_83])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, (~r2_relset_1(esk5_0,esk6_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_83]), c_0_84])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_85]), c_0_86]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 88
% 0.13/0.39  # Proof object clause steps            : 62
% 0.13/0.39  # Proof object formula steps           : 26
% 0.13/0.39  # Proof object conjectures             : 42
% 0.13/0.39  # Proof object clause conjectures      : 39
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 23
% 0.13/0.39  # Proof object initial formulas used   : 13
% 0.13/0.39  # Proof object generating inferences   : 36
% 0.13/0.39  # Proof object simplifying inferences  : 33
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 13
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 33
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 33
% 0.13/0.39  # Processed clauses                    : 195
% 0.13/0.39  # ...of these trivial                  : 5
% 0.13/0.39  # ...subsumed                          : 64
% 0.13/0.39  # ...remaining for further processing  : 126
% 0.13/0.39  # Other redundant clauses eliminated   : 26
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 7
% 0.13/0.39  # Backward-rewritten                   : 60
% 0.13/0.39  # Generated clauses                    : 398
% 0.13/0.39  # ...of the previous two non-trivial   : 365
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 370
% 0.13/0.39  # Factorizations                       : 1
% 0.13/0.39  # Equation resolutions                 : 28
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 52
% 0.13/0.39  #    Positive orientable unit clauses  : 8
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 43
% 0.13/0.39  # Current number of unprocessed clauses: 183
% 0.13/0.39  # ...number of literals in the above   : 748
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 67
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 2167
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 1150
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 91
% 0.13/0.39  # Unit Clause-clause subsumption calls : 49
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 20
% 0.13/0.39  # BW rewrite match successes           : 4
% 0.13/0.39  # Condensation attempts                : 195
% 0.13/0.39  # Condensation successes               : 18
% 0.13/0.39  # Termbank termtop insertions          : 8198
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.041 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.045 s
% 0.13/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
