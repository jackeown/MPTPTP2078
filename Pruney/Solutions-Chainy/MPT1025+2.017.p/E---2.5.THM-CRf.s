%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:37 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 151 expanded)
%              Number of clauses        :   38 (  60 expanded)
%              Number of leaves         :   13 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  264 ( 755 expanded)
%              Number of equality atoms :   66 ( 145 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t116_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ( m1_subset_1(X6,X1)
               => ~ ( r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ~ ( r2_hidden(X6,X3)
                      & X5 = k1_funct_1(X4,X6) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t116_funct_2])).

fof(c_0_14,plain,(
    ! [X54,X55,X56] :
      ( ( v4_relat_1(X56,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( v5_relat_1(X56,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_15,negated_conjecture,(
    ! [X72] :
      ( v1_funct_1(esk12_0)
      & v1_funct_2(esk12_0,esk9_0,esk10_0)
      & m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))
      & r2_hidden(esk13_0,k7_relset_1(esk9_0,esk10_0,esk12_0,esk11_0))
      & ( ~ m1_subset_1(X72,esk9_0)
        | ~ r2_hidden(X72,esk11_0)
        | esk13_0 != k1_funct_1(esk12_0,X72) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | v1_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,plain,(
    ! [X57,X58,X59] :
      ( ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))
      | k1_relset_1(X57,X58,X59) = k1_relat_1(X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_18,plain,(
    ! [X64,X65,X66] :
      ( ( ~ v1_funct_2(X66,X64,X65)
        | X64 = k1_relset_1(X64,X65,X66)
        | X65 = k1_xboole_0
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( X64 != k1_relset_1(X64,X65,X66)
        | v1_funct_2(X66,X64,X65)
        | X65 = k1_xboole_0
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( ~ v1_funct_2(X66,X64,X65)
        | X64 = k1_relset_1(X64,X65,X66)
        | X64 != k1_xboole_0
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( X64 != k1_relset_1(X64,X65,X66)
        | v1_funct_2(X66,X64,X65)
        | X64 != k1_xboole_0
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( ~ v1_funct_2(X66,X64,X65)
        | X66 = k1_xboole_0
        | X64 = k1_xboole_0
        | X65 != k1_xboole_0
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) )
      & ( X66 != k1_xboole_0
        | v1_funct_2(X66,X64,X65)
        | X64 = k1_xboole_0
        | X65 != k1_xboole_0
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_19,plain,(
    ! [X43,X44,X45] :
      ( ~ v1_relat_1(X44)
      | ~ v5_relat_1(X44,X43)
      | ~ v1_funct_1(X44)
      | ~ r2_hidden(X45,k1_relat_1(X44))
      | r2_hidden(k1_funct_1(X44,X45),X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_20,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ r1_tarski(X50,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_26,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_27,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_28,plain,(
    ! [X16,X17,X18,X20] :
      ( ( r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X18))
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X16),X18)
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | ~ r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(X20,k1_relat_1(X18))
        | ~ r2_hidden(k4_tarski(X20,X16),X18)
        | ~ r2_hidden(X20,X17)
        | r2_hidden(X16,k9_relat_1(X18,X17))
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

fof(c_0_29,plain,(
    ! [X60,X61,X62,X63] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))
      | k7_relset_1(X60,X61,X62,X63) = k9_relat_1(X62,X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_30,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( v5_relat_1(esk12_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_34,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk12_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk13_0,k7_relset_1(esk9_0,esk10_0,esk12_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk12_0,X1),esk10_0)
    | ~ r2_hidden(X1,k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_43,negated_conjecture,
    ( esk9_0 = k1_relat_1(esk12_0)
    | esk10_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_21])])).

cnf(c_0_44,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,X3))
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk13_0,k9_relat_1(esk12_0,esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_21])])).

cnf(c_0_47,negated_conjecture,
    ( esk9_0 = k1_relat_1(esk12_0)
    | ~ r2_hidden(X1,k1_relat_1(esk12_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(k1_relat_1(esk12_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_33])])).

cnf(c_0_50,negated_conjecture,
    ( ~ m1_subset_1(X1,esk9_0)
    | ~ r2_hidden(X1,esk11_0)
    | esk13_0 != k1_funct_1(esk12_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( esk9_0 = k1_relat_1(esk12_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_52,plain,(
    ! [X21,X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( r2_hidden(esk3_4(X21,X22,X23,X24),k1_relat_1(X21))
        | ~ r2_hidden(X24,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk3_4(X21,X22,X23,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( X24 = k1_funct_1(X21,esk3_4(X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(X27,k1_relat_1(X21))
        | ~ r2_hidden(X27,X22)
        | X26 != k1_funct_1(X21,X27)
        | r2_hidden(X26,X23)
        | X23 != k9_relat_1(X21,X22)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ r2_hidden(esk4_3(X21,X28,X29),X29)
        | ~ r2_hidden(X31,k1_relat_1(X21))
        | ~ r2_hidden(X31,X28)
        | esk4_3(X21,X28,X29) != k1_funct_1(X21,X31)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk5_3(X21,X28,X29),k1_relat_1(X21))
        | r2_hidden(esk4_3(X21,X28,X29),X29)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( r2_hidden(esk5_3(X21,X28,X29),X28)
        | r2_hidden(esk4_3(X21,X28,X29),X29)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( esk4_3(X21,X28,X29) = k1_funct_1(X21,esk5_3(X21,X28,X29))
        | r2_hidden(esk4_3(X21,X28,X29),X29)
        | X29 = k9_relat_1(X21,X28)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( esk13_0 != k1_funct_1(esk12_0,X1)
    | ~ m1_subset_1(X1,k1_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_54,plain,
    ( X1 = k1_funct_1(X2,esk3_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_55,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,X13)
      | m1_subset_1(X12,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_56,negated_conjecture,
    ( X1 != k9_relat_1(esk12_0,X2)
    | esk13_0 != X3
    | ~ m1_subset_1(esk3_4(esk12_0,X2,X1,X3),k1_relat_1(esk12_0))
    | ~ r2_hidden(esk3_4(esk12_0,X2,X1,X3),esk11_0)
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_32]),c_0_33])])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( X1 != k9_relat_1(esk12_0,X2)
    | esk13_0 != X3
    | ~ r2_hidden(esk3_4(esk12_0,X2,X1,X3),k1_relat_1(esk12_0))
    | ~ r2_hidden(esk3_4(esk12_0,X2,X1,X3),esk11_0)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_59,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( X1 != k9_relat_1(esk12_0,esk11_0)
    | esk13_0 != X2
    | ~ r2_hidden(esk3_4(esk12_0,esk11_0,X1,X2),k1_relat_1(esk12_0))
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_32]),c_0_33])])).

cnf(c_0_61,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( X1 != k9_relat_1(esk12_0,esk11_0)
    | esk13_0 != X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_32]),c_0_33])])).

cnf(c_0_63,negated_conjecture,
    ( esk13_0 != X1
    | ~ r2_hidden(X1,k9_relat_1(esk12_0,esk11_0)) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_63,c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 4.28/4.51  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 4.28/4.51  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.28/4.51  #
% 4.28/4.51  # Preprocessing time       : 0.030 s
% 4.28/4.51  # Presaturation interreduction done
% 4.28/4.51  
% 4.28/4.51  # Proof found!
% 4.28/4.51  # SZS status Theorem
% 4.28/4.51  # SZS output start CNFRefutation
% 4.28/4.51  fof(t116_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 4.28/4.51  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.28/4.51  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.28/4.51  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.28/4.51  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.28/4.51  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 4.28/4.51  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.28/4.51  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.28/4.51  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.28/4.51  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.28/4.51  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.28/4.51  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 4.28/4.51  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.28/4.51  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:(m1_subset_1(X6,X1)=>~((r2_hidden(X6,X3)&X5=k1_funct_1(X4,X6)))))))), inference(assume_negation,[status(cth)],[t116_funct_2])).
% 4.28/4.51  fof(c_0_14, plain, ![X54, X55, X56]:((v4_relat_1(X56,X54)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(v5_relat_1(X56,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 4.28/4.51  fof(c_0_15, negated_conjecture, ![X72]:(((v1_funct_1(esk12_0)&v1_funct_2(esk12_0,esk9_0,esk10_0))&m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))))&(r2_hidden(esk13_0,k7_relset_1(esk9_0,esk10_0,esk12_0,esk11_0))&(~m1_subset_1(X72,esk9_0)|(~r2_hidden(X72,esk11_0)|esk13_0!=k1_funct_1(esk12_0,X72))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 4.28/4.51  fof(c_0_16, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|v1_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 4.28/4.51  fof(c_0_17, plain, ![X57, X58, X59]:(~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X58)))|k1_relset_1(X57,X58,X59)=k1_relat_1(X59)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 4.28/4.51  fof(c_0_18, plain, ![X64, X65, X66]:((((~v1_funct_2(X66,X64,X65)|X64=k1_relset_1(X64,X65,X66)|X65=k1_xboole_0|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))&(X64!=k1_relset_1(X64,X65,X66)|v1_funct_2(X66,X64,X65)|X65=k1_xboole_0|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))&((~v1_funct_2(X66,X64,X65)|X64=k1_relset_1(X64,X65,X66)|X64!=k1_xboole_0|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))&(X64!=k1_relset_1(X64,X65,X66)|v1_funct_2(X66,X64,X65)|X64!=k1_xboole_0|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))))&((~v1_funct_2(X66,X64,X65)|X66=k1_xboole_0|X64=k1_xboole_0|X65!=k1_xboole_0|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65))))&(X66!=k1_xboole_0|v1_funct_2(X66,X64,X65)|X64=k1_xboole_0|X65!=k1_xboole_0|~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 4.28/4.51  fof(c_0_19, plain, ![X43, X44, X45]:(~v1_relat_1(X44)|~v5_relat_1(X44,X43)|~v1_funct_1(X44)|(~r2_hidden(X45,k1_relat_1(X44))|r2_hidden(k1_funct_1(X44,X45),X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 4.28/4.51  cnf(c_0_20, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 4.28/4.51  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk12_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.28/4.51  cnf(c_0_22, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 4.28/4.51  cnf(c_0_23, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 4.28/4.51  cnf(c_0_24, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 4.28/4.51  fof(c_0_25, plain, ![X49, X50]:(~r2_hidden(X49,X50)|~r1_tarski(X50,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 4.28/4.51  fof(c_0_26, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 4.28/4.51  fof(c_0_27, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 4.28/4.51  fof(c_0_28, plain, ![X16, X17, X18, X20]:((((r2_hidden(esk2_3(X16,X17,X18),k1_relat_1(X18))|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk2_3(X16,X17,X18),X16),X18)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(r2_hidden(esk2_3(X16,X17,X18),X17)|~r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18)))&(~r2_hidden(X20,k1_relat_1(X18))|~r2_hidden(k4_tarski(X20,X16),X18)|~r2_hidden(X20,X17)|r2_hidden(X16,k9_relat_1(X18,X17))|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 4.28/4.51  fof(c_0_29, plain, ![X60, X61, X62, X63]:(~m1_subset_1(X62,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))|k7_relset_1(X60,X61,X62,X63)=k9_relat_1(X62,X63)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 4.28/4.51  cnf(c_0_30, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 4.28/4.51  cnf(c_0_31, negated_conjecture, (v5_relat_1(esk12_0,esk10_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 4.28/4.51  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.28/4.51  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk12_0)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 4.28/4.51  cnf(c_0_34, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 4.28/4.51  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk12_0,esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.28/4.51  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.28/4.51  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.28/4.51  cnf(c_0_38, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.28/4.51  cnf(c_0_39, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 4.28/4.51  cnf(c_0_40, negated_conjecture, (r2_hidden(esk13_0,k7_relset_1(esk9_0,esk10_0,esk12_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.28/4.51  cnf(c_0_41, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.28/4.51  cnf(c_0_42, negated_conjecture, (r2_hidden(k1_funct_1(esk12_0,X1),esk10_0)|~r2_hidden(X1,k1_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])])).
% 4.28/4.51  cnf(c_0_43, negated_conjecture, (esk9_0=k1_relat_1(esk12_0)|esk10_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_21])])).
% 4.28/4.51  cnf(c_0_44, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 4.28/4.51  cnf(c_0_45, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,X3))|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 4.28/4.51  cnf(c_0_46, negated_conjecture, (r2_hidden(esk13_0,k9_relat_1(esk12_0,esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_21])])).
% 4.28/4.51  cnf(c_0_47, negated_conjecture, (esk9_0=k1_relat_1(esk12_0)|~r2_hidden(X1,k1_relat_1(esk12_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 4.28/4.51  cnf(c_0_48, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.28/4.51  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(k1_relat_1(esk12_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_33])])).
% 4.28/4.51  cnf(c_0_50, negated_conjecture, (~m1_subset_1(X1,esk9_0)|~r2_hidden(X1,esk11_0)|esk13_0!=k1_funct_1(esk12_0,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 4.28/4.51  cnf(c_0_51, negated_conjecture, (esk9_0=k1_relat_1(esk12_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 4.28/4.51  fof(c_0_52, plain, ![X21, X22, X23, X24, X26, X27, X28, X29, X31]:(((((r2_hidden(esk3_4(X21,X22,X23,X24),k1_relat_1(X21))|~r2_hidden(X24,X23)|X23!=k9_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(esk3_4(X21,X22,X23,X24),X22)|~r2_hidden(X24,X23)|X23!=k9_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(X24=k1_funct_1(X21,esk3_4(X21,X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k9_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(~r2_hidden(X27,k1_relat_1(X21))|~r2_hidden(X27,X22)|X26!=k1_funct_1(X21,X27)|r2_hidden(X26,X23)|X23!=k9_relat_1(X21,X22)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&((~r2_hidden(esk4_3(X21,X28,X29),X29)|(~r2_hidden(X31,k1_relat_1(X21))|~r2_hidden(X31,X28)|esk4_3(X21,X28,X29)!=k1_funct_1(X21,X31))|X29=k9_relat_1(X21,X28)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(((r2_hidden(esk5_3(X21,X28,X29),k1_relat_1(X21))|r2_hidden(esk4_3(X21,X28,X29),X29)|X29=k9_relat_1(X21,X28)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(r2_hidden(esk5_3(X21,X28,X29),X28)|r2_hidden(esk4_3(X21,X28,X29),X29)|X29=k9_relat_1(X21,X28)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(esk4_3(X21,X28,X29)=k1_funct_1(X21,esk5_3(X21,X28,X29))|r2_hidden(esk4_3(X21,X28,X29),X29)|X29=k9_relat_1(X21,X28)|(~v1_relat_1(X21)|~v1_funct_1(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 4.28/4.51  cnf(c_0_53, negated_conjecture, (esk13_0!=k1_funct_1(esk12_0,X1)|~m1_subset_1(X1,k1_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 4.28/4.51  cnf(c_0_54, plain, (X1=k1_funct_1(X2,esk3_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 4.28/4.51  fof(c_0_55, plain, ![X12, X13]:(~r2_hidden(X12,X13)|m1_subset_1(X12,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 4.28/4.51  cnf(c_0_56, negated_conjecture, (X1!=k9_relat_1(esk12_0,X2)|esk13_0!=X3|~m1_subset_1(esk3_4(esk12_0,X2,X1,X3),k1_relat_1(esk12_0))|~r2_hidden(esk3_4(esk12_0,X2,X1,X3),esk11_0)|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_32]), c_0_33])])).
% 4.28/4.51  cnf(c_0_57, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 4.28/4.51  cnf(c_0_58, negated_conjecture, (X1!=k9_relat_1(esk12_0,X2)|esk13_0!=X3|~r2_hidden(esk3_4(esk12_0,X2,X1,X3),k1_relat_1(esk12_0))|~r2_hidden(esk3_4(esk12_0,X2,X1,X3),esk11_0)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 4.28/4.51  cnf(c_0_59, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 4.28/4.51  cnf(c_0_60, negated_conjecture, (X1!=k9_relat_1(esk12_0,esk11_0)|esk13_0!=X2|~r2_hidden(esk3_4(esk12_0,esk11_0,X1,X2),k1_relat_1(esk12_0))|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_32]), c_0_33])])).
% 4.28/4.51  cnf(c_0_61, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 4.28/4.51  cnf(c_0_62, negated_conjecture, (X1!=k9_relat_1(esk12_0,esk11_0)|esk13_0!=X2|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_32]), c_0_33])])).
% 4.28/4.51  cnf(c_0_63, negated_conjecture, (esk13_0!=X1|~r2_hidden(X1,k9_relat_1(esk12_0,esk11_0))), inference(er,[status(thm)],[c_0_62])).
% 4.28/4.51  cnf(c_0_64, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_63, c_0_46]), ['proof']).
% 4.28/4.51  # SZS output end CNFRefutation
% 4.28/4.51  # Proof object total steps             : 65
% 4.28/4.51  # Proof object clause steps            : 38
% 4.28/4.51  # Proof object formula steps           : 27
% 4.28/4.51  # Proof object conjectures             : 23
% 4.28/4.51  # Proof object clause conjectures      : 20
% 4.28/4.51  # Proof object formula conjectures     : 3
% 4.28/4.51  # Proof object initial clauses used    : 20
% 4.28/4.51  # Proof object initial formulas used   : 13
% 4.28/4.51  # Proof object generating inferences   : 17
% 4.28/4.51  # Proof object simplifying inferences  : 21
% 4.28/4.51  # Training examples: 0 positive, 0 negative
% 4.28/4.51  # Parsed axioms                        : 16
% 4.28/4.51  # Removed by relevancy pruning/SinE    : 0
% 4.28/4.51  # Initial clauses                      : 42
% 4.28/4.51  # Removed in clause preprocessing      : 0
% 4.28/4.51  # Initial clauses in saturation        : 42
% 4.28/4.51  # Processed clauses                    : 13831
% 4.28/4.51  # ...of these trivial                  : 23
% 4.28/4.51  # ...subsumed                          : 11737
% 4.28/4.51  # ...remaining for further processing  : 2071
% 4.28/4.51  # Other redundant clauses eliminated   : 4
% 4.28/4.51  # Clauses deleted for lack of memory   : 0
% 4.28/4.51  # Backward-subsumed                    : 134
% 4.28/4.51  # Backward-rewritten                   : 13
% 4.28/4.51  # Generated clauses                    : 302523
% 4.28/4.51  # ...of the previous two non-trivial   : 301142
% 4.28/4.51  # Contextual simplify-reflections      : 88
% 4.28/4.51  # Paramodulations                      : 302280
% 4.28/4.51  # Factorizations                       : 8
% 4.28/4.51  # Equation resolutions                 : 235
% 4.28/4.51  # Propositional unsat checks           : 0
% 4.28/4.51  #    Propositional check models        : 0
% 4.28/4.51  #    Propositional check unsatisfiable : 0
% 4.28/4.51  #    Propositional clauses             : 0
% 4.28/4.51  #    Propositional clauses after purity: 0
% 4.28/4.51  #    Propositional unsat core size     : 0
% 4.28/4.51  #    Propositional preprocessing time  : 0.000
% 4.28/4.51  #    Propositional encoding time       : 0.000
% 4.28/4.51  #    Propositional solver time         : 0.000
% 4.28/4.51  #    Success case prop preproc time    : 0.000
% 4.28/4.51  #    Success case prop encoding time   : 0.000
% 4.28/4.51  #    Success case prop solver time     : 0.000
% 4.28/4.51  # Current number of processed clauses  : 1882
% 4.28/4.51  #    Positive orientable unit clauses  : 16
% 4.28/4.51  #    Positive unorientable unit clauses: 0
% 4.28/4.51  #    Negative unit clauses             : 17
% 4.28/4.51  #    Non-unit-clauses                  : 1849
% 4.28/4.51  # Current number of unprocessed clauses: 286904
% 4.28/4.51  # ...number of literals in the above   : 2716387
% 4.28/4.51  # Current number of archived formulas  : 0
% 4.28/4.51  # Current number of archived clauses   : 189
% 4.28/4.51  # Clause-clause subsumption calls (NU) : 1608897
% 4.28/4.51  # Rec. Clause-clause subsumption calls : 70049
% 4.28/4.51  # Non-unit clause-clause subsumptions  : 9462
% 4.28/4.51  # Unit Clause-clause subsumption calls : 508
% 4.28/4.51  # Rewrite failures with RHS unbound    : 0
% 4.28/4.51  # BW rewrite match attempts            : 1
% 4.28/4.51  # BW rewrite match successes           : 1
% 4.28/4.51  # Condensation attempts                : 0
% 4.28/4.51  # Condensation successes               : 0
% 4.28/4.51  # Termbank termtop insertions          : 7562971
% 4.28/4.53  
% 4.28/4.53  # -------------------------------------------------
% 4.28/4.53  # User time                : 4.033 s
% 4.28/4.53  # System time              : 0.148 s
% 4.28/4.53  # Total time               : 4.181 s
% 4.28/4.53  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
