%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:06 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 (1426 expanded)
%              Number of clauses        :   50 ( 587 expanded)
%              Number of leaves         :   12 ( 337 expanded)
%              Depth                    :   20
%              Number of atoms          :  215 (5765 expanded)
%              Number of equality atoms :   81 (1459 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t190_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X2,X3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
          & ! [X5] :
              ( m1_subset_1(X5,X2)
             => X1 != k1_funct_1(X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
       => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
            & ! [X5] :
                ( m1_subset_1(X5,X2)
               => X1 != k1_funct_1(X4,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t190_funct_2])).

fof(c_0_13,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v1_funct_2(X32,X30,X31)
        | X30 = k1_relset_1(X30,X31,X32)
        | X31 = k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X30 != k1_relset_1(X30,X31,X32)
        | v1_funct_2(X32,X30,X31)
        | X31 = k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ v1_funct_2(X32,X30,X31)
        | X30 = k1_relset_1(X30,X31,X32)
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X30 != k1_relset_1(X30,X31,X32)
        | v1_funct_2(X32,X30,X31)
        | X30 != k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ v1_funct_2(X32,X30,X31)
        | X32 = k1_xboole_0
        | X30 = k1_xboole_0
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X32 != k1_xboole_0
        | v1_funct_2(X32,X30,X31)
        | X30 = k1_xboole_0
        | X31 != k1_xboole_0
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_14,negated_conjecture,(
    ! [X37] :
      ( v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,esk4_0,esk5_0)
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk3_0,k2_relset_1(esk4_0,esk5_0,esk6_0))
      & ( ~ m1_subset_1(X37,esk4_0)
        | esk3_0 != k1_funct_1(esk6_0,X37) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k1_relset_1(X24,X25,X26) = k1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_16,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k2_relset_1(X27,X28,X29) = k2_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_17,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | v1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_22,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k9_relat_1(X17,k1_relat_1(X17)) = k2_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_24,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk3_0,k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = k2_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_29,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_18])).

fof(c_0_32,plain,(
    ! [X12,X13,X14,X16] :
      ( ( r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X14))
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X12),X14)
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(X16,k1_relat_1(X14))
        | ~ r2_hidden(k4_tarski(X16,X12),X14)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_0,k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(esk6_0) = k9_relat_1(esk6_0,esk4_0)
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

fof(c_0_35,plain,(
    ! [X18,X19,X20] :
      ( ( r2_hidden(X18,k1_relat_1(X20))
        | ~ r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( X19 = k1_funct_1(X20,X18)
        | ~ r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( ~ r2_hidden(X18,k1_relat_1(X20))
        | X19 != k1_funct_1(X20,X18)
        | r2_hidden(k4_tarski(X18,X19),X20)
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk3_0,k9_relat_1(esk6_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_38,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | m1_subset_1(X10,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( X1 = k1_funct_1(X2,X3)
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(k4_tarski(esk2_3(esk3_0,esk4_0,esk6_0),esk3_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_31])])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_37]),c_0_31])])).

cnf(c_0_45,negated_conjecture,
    ( ~ m1_subset_1(X1,esk4_0)
    | esk3_0 != k1_funct_1(esk6_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,negated_conjecture,
    ( k1_funct_1(esk6_0,esk2_3(esk3_0,esk4_0,esk6_0)) = esk3_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_31])])).

cnf(c_0_47,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_49,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_49])).

cnf(c_0_53,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_55,negated_conjecture,
    ( k1_relset_1(esk4_0,k1_xboole_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(rw,[status(thm)],[c_0_25,c_0_49])).

cnf(c_0_56,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | v1_funct_2(esk6_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk6_0) = k1_relat_1(esk6_0)
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk6_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

fof(c_0_62,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk6_0) = k9_relat_1(esk6_0,k1_xboole_0)
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_61]),c_0_31])])).

cnf(c_0_64,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk3_0,k9_relat_1(esk6_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_63])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(k2_relset_1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_27])).

cnf(c_0_67,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk2_3(esk3_0,k1_xboole_0,esk6_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_65]),c_0_31])])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(k2_relat_1(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_66,c_0_28])).

cnf(c_0_70,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_67]),c_0_68])])).

cnf(c_0_71,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_68])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:34:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.37  # and selection function SelectNewComplexAHPNS.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t190_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 0.19/0.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.37  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.37  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.19/0.37  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.19/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.19/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.37  fof(c_0_12, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5)))))), inference(assume_negation,[status(cth)],[t190_funct_2])).
% 0.19/0.37  fof(c_0_13, plain, ![X30, X31, X32]:((((~v1_funct_2(X32,X30,X31)|X30=k1_relset_1(X30,X31,X32)|X31=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(X30!=k1_relset_1(X30,X31,X32)|v1_funct_2(X32,X30,X31)|X31=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&((~v1_funct_2(X32,X30,X31)|X30=k1_relset_1(X30,X31,X32)|X30!=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(X30!=k1_relset_1(X30,X31,X32)|v1_funct_2(X32,X30,X31)|X30!=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&((~v1_funct_2(X32,X30,X31)|X32=k1_xboole_0|X30=k1_xboole_0|X31!=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(X32!=k1_xboole_0|v1_funct_2(X32,X30,X31)|X30=k1_xboole_0|X31!=k1_xboole_0|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.37  fof(c_0_14, negated_conjecture, ![X37]:(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&(r2_hidden(esk3_0,k2_relset_1(esk4_0,esk5_0,esk6_0))&(~m1_subset_1(X37,esk4_0)|esk3_0!=k1_funct_1(esk6_0,X37)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])).
% 0.19/0.37  fof(c_0_15, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k1_relset_1(X24,X25,X26)=k1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.37  fof(c_0_16, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k2_relset_1(X27,X28,X29)=k2_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.37  cnf(c_0_17, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_20, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  fof(c_0_21, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|v1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.37  cnf(c_0_22, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.37  fof(c_0_23, plain, ![X17]:(~v1_relat_1(X17)|k9_relat_1(X17,k1_relat_1(X17))=k2_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_20, c_0_18])).
% 0.19/0.37  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (r2_hidden(esk3_0,k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=k2_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.19/0.37  cnf(c_0_29, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_26, c_0_18])).
% 0.19/0.37  fof(c_0_32, plain, ![X12, X13, X14, X16]:((((r2_hidden(esk2_3(X12,X13,X14),k1_relat_1(X14))|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk2_3(X12,X13,X14),X12),X14)|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14)))&(r2_hidden(esk2_3(X12,X13,X14),X13)|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14)))&(~r2_hidden(X16,k1_relat_1(X14))|~r2_hidden(k4_tarski(X16,X12),X14)|~r2_hidden(X16,X13)|r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (r2_hidden(esk3_0,k2_relat_1(esk6_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (k2_relat_1(esk6_0)=k9_relat_1(esk6_0,esk4_0)|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.19/0.37  fof(c_0_35, plain, ![X18, X19, X20]:(((r2_hidden(X18,k1_relat_1(X20))|~r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(X19=k1_funct_1(X20,X18)|~r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20))))&(~r2_hidden(X18,k1_relat_1(X20))|X19!=k1_funct_1(X20,X18)|r2_hidden(k4_tarski(X18,X19),X20)|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.19/0.37  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk2_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk3_0,k9_relat_1(esk6_0,esk4_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.37  fof(c_0_38, plain, ![X10, X11]:(~r2_hidden(X10,X11)|m1_subset_1(X10,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.19/0.37  cnf(c_0_39, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.37  cnf(c_0_40, plain, (X1=k1_funct_1(X2,X3)|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(k4_tarski(esk2_3(esk3_0,esk4_0,esk6_0),esk3_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_31])])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_43, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (esk5_0=k1_xboole_0|r2_hidden(esk2_3(esk3_0,esk4_0,esk6_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_37]), c_0_31])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (~m1_subset_1(X1,esk4_0)|esk3_0!=k1_funct_1(esk6_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_46, negated_conjecture, (k1_funct_1(esk6_0,esk2_3(esk3_0,esk4_0,esk6_0))=esk3_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_31])])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(esk2_3(esk3_0,esk4_0,esk6_0),esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.37  cnf(c_0_48, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (esk5_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])).
% 0.19/0.37  cnf(c_0_50, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_19, c_0_49])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_18, c_0_49])).
% 0.19/0.37  cnf(c_0_53, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, (esk6_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (k1_relset_1(esk4_0,k1_xboole_0,esk6_0)=k1_relat_1(esk6_0)), inference(rw,[status(thm)],[c_0_25, c_0_49])).
% 0.19/0.37  cnf(c_0_56, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_53])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (esk6_0=k1_xboole_0|v1_funct_2(esk6_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_54])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (esk6_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_52, c_0_54])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk6_0)=k1_relat_1(esk6_0)|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_54])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk6_0)=k1_xboole_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.37  fof(c_0_62, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.37  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk6_0)=k9_relat_1(esk6_0,k1_xboole_0)|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_61]), c_0_31])])).
% 0.19/0.37  cnf(c_0_64, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.37  cnf(c_0_65, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk3_0,k9_relat_1(esk6_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_63])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(k2_relset_1(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_64, c_0_27])).
% 0.19/0.37  cnf(c_0_67, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk2_3(esk3_0,k1_xboole_0,esk6_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_65]), c_0_31])])).
% 0.19/0.37  cnf(c_0_68, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(k2_relat_1(esk6_0))), inference(rw,[status(thm)],[c_0_66, c_0_28])).
% 0.19/0.37  cnf(c_0_70, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_67]), c_0_68])])).
% 0.19/0.37  cnf(c_0_71, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.37  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_68])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 73
% 0.19/0.37  # Proof object clause steps            : 50
% 0.19/0.37  # Proof object formula steps           : 23
% 0.19/0.37  # Proof object conjectures             : 37
% 0.19/0.37  # Proof object clause conjectures      : 34
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 19
% 0.19/0.37  # Proof object initial formulas used   : 12
% 0.19/0.37  # Proof object generating inferences   : 23
% 0.19/0.37  # Proof object simplifying inferences  : 32
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 12
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 28
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 28
% 0.19/0.37  # Processed clauses                    : 91
% 0.19/0.37  # ...of these trivial                  : 2
% 0.19/0.37  # ...subsumed                          : 12
% 0.19/0.37  # ...remaining for further processing  : 77
% 0.19/0.37  # Other redundant clauses eliminated   : 6
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 44
% 0.19/0.37  # Generated clauses                    : 84
% 0.19/0.37  # ...of the previous two non-trivial   : 91
% 0.19/0.37  # Contextual simplify-reflections      : 2
% 0.19/0.37  # Paramodulations                      : 79
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 6
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 28
% 0.19/0.37  #    Positive orientable unit clauses  : 5
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 0
% 0.19/0.37  #    Non-unit-clauses                  : 23
% 0.19/0.37  # Current number of unprocessed clauses: 18
% 0.19/0.37  # ...number of literals in the above   : 58
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 44
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 151
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 108
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.37  # Unit Clause-clause subsumption calls : 9
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 4
% 0.19/0.37  # BW rewrite match successes           : 4
% 0.19/0.37  # Condensation attempts                : 91
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3002
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.031 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
