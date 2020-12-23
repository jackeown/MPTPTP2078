%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:43 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  122 (1193 expanded)
%              Number of clauses        :   82 ( 491 expanded)
%              Number of leaves         :   20 ( 301 expanded)
%              Depth                    :   16
%              Number of atoms          :  308 (4846 expanded)
%              Number of equality atoms :   94 ( 580 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t178_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ~ v1_xboole_0(X4)
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X1,X4)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) )
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k7_relset_1(X1,X4,X5,X2),X3) )
           => ( v1_funct_1(k2_partfun1(X1,X4,X5,X2))
              & v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3)
              & m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ~ v1_xboole_0(X4)
       => ! [X5] :
            ( ( v1_funct_1(X5)
              & v1_funct_2(X5,X1,X4)
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) )
           => ( ( r1_tarski(X2,X1)
                & r1_tarski(k7_relset_1(X1,X4,X5,X2),X3) )
             => ( v1_funct_1(k2_partfun1(X1,X4,X5,X2))
                & v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3)
                & m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t178_funct_2])).

fof(c_0_21,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k2_partfun1(X47,X48,X49,X50) = k7_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk1_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0)))
    & r1_tarski(esk2_0,esk1_0)
    & r1_tarski(k7_relset_1(esk1_0,esk4_0,esk5_0,esk2_0),esk3_0)
    & ( ~ v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0))
      | ~ v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)
      | ~ m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

fof(c_0_23,plain,(
    ! [X43,X44,X45,X46] :
      ( ( v1_funct_1(k2_partfun1(X43,X44,X45,X46))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( m1_subset_1(k2_partfun1(X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_24,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k7_relset_1(X33,X34,X35,X36) = k9_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_28,plain,(
    ! [X27,X28,X29] :
      ( ( v4_relat_1(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( v5_relat_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k2_partfun1(esk1_0,esk4_0,esk5_0,X1) = k7_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_32,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_33,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ r1_tarski(k1_relat_1(X39),X37)
      | ~ r1_tarski(k2_relat_1(X39),X38)
      | m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_34,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | k2_relat_1(k7_relat_1(X20,X19)) = k9_relat_1(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_35,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | v1_relat_1(k7_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_36,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v4_relat_1(X22,X21)
      | X22 = k7_relat_1(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_38,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_30]),c_0_26])])).

cnf(c_0_40,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk4_0,esk5_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( k7_relset_1(esk1_0,esk4_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_47,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_48,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_49,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | r1_tarski(k1_relat_1(k7_relat_1(X24,X23)),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_50,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk5_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_41])])).

cnf(c_0_53,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ r1_tarski(k9_relat_1(X1,X2),X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_25]),c_0_41])])).

cnf(c_0_56,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_25]),c_0_26])])).

fof(c_0_58,plain,(
    ! [X40,X41,X42] :
      ( ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X42 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X42 != k1_xboole_0
        | v1_funct_2(X42,X40,X41)
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_59,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_60,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_61,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_62,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_63,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk5_0,X1),esk1_0) = k7_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk5_0,esk2_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

fof(c_0_67,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(X25,k1_relat_1(X26))
      | k1_relat_1(k7_relat_1(X26,X25)) = X25 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_68,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( k1_relset_1(esk1_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_25])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(esk5_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk5_0,X1)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_52])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_63]),c_0_55])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk2_0),esk2_0,esk3_0)
    | ~ m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_30]),c_0_30])).

cnf(c_0_77,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk1_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_25]),c_0_69]),c_0_70])])).

cnf(c_0_79,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_80,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_73])).

fof(c_0_81,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_74])).

cnf(c_0_84,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_85,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,k7_relat_1(esk5_0,esk2_0)) = k1_relat_1(k7_relat_1(esk5_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_75])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk2_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_75])])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,X1)) = X1
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_55])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_89,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_79])).

cnf(c_0_90,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_80])).

cnf(c_0_91,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk5_0,esk2_0),k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_relat_1(k7_relat_1(esk5_0,esk2_0)) != esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_75])]),c_0_86])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,esk2_0)) = esk2_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_89]),c_0_90])])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( k7_relat_1(esk5_0,esk2_0) = k2_zfmisc_1(esk1_0,esk3_0)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),k7_relat_1(esk5_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_72])).

cnf(c_0_101,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_96]),c_0_90])])).

cnf(c_0_102,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( k7_relat_1(esk5_0,esk2_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_80]),c_0_80]),c_0_72])])).

cnf(c_0_104,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_97])).

cnf(c_0_106,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_108,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_103]),c_0_104])).

cnf(c_0_109,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_110,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_105])).

cnf(c_0_111,plain,
    ( k1_relat_1(k7_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_63])).

cnf(c_0_112,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_106])).

cnf(c_0_113,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_114,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])])).

cnf(c_0_115,plain,
    ( r1_tarski(k7_relat_1(X1,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112]),c_0_44])).

cnf(c_0_116,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_113]),c_0_112])).

cnf(c_0_117,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_79]),c_0_104])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,k1_xboole_0),k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_114]),c_0_114])).

cnf(c_0_119,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_115]),c_0_72])])).

cnf(c_0_120,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_79])])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:04:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.40  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.18/0.40  # and selection function SelectNewComplexAHP.
% 0.18/0.40  #
% 0.18/0.40  # Preprocessing time       : 0.028 s
% 0.18/0.40  # Presaturation interreduction done
% 0.18/0.40  
% 0.18/0.40  # Proof found!
% 0.18/0.40  # SZS status Theorem
% 0.18/0.40  # SZS output start CNFRefutation
% 0.18/0.40  fof(t178_funct_2, conjecture, ![X1, X2, X3, X4]:(~(v1_xboole_0(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=>((r1_tarski(X2,X1)&r1_tarski(k7_relset_1(X1,X4,X5,X2),X3))=>((v1_funct_1(k2_partfun1(X1,X4,X5,X2))&v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3))&m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 0.18/0.40  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.18/0.40  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.18/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.18/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.18/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.18/0.40  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.18/0.40  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.18/0.40  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.18/0.40  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.18/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.18/0.40  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.18/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.18/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.40  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.18/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.18/0.40  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(~(v1_xboole_0(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=>((r1_tarski(X2,X1)&r1_tarski(k7_relset_1(X1,X4,X5,X2),X3))=>((v1_funct_1(k2_partfun1(X1,X4,X5,X2))&v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3))&m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))), inference(assume_negation,[status(cth)],[t178_funct_2])).
% 0.18/0.40  fof(c_0_21, plain, ![X47, X48, X49, X50]:(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k2_partfun1(X47,X48,X49,X50)=k7_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.18/0.40  fof(c_0_22, negated_conjecture, (~v1_xboole_0(esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk1_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0))))&((r1_tarski(esk2_0,esk1_0)&r1_tarski(k7_relset_1(esk1_0,esk4_0,esk5_0,esk2_0),esk3_0))&(~v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0))|~v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)|~m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.18/0.40  fof(c_0_23, plain, ![X43, X44, X45, X46]:((v1_funct_1(k2_partfun1(X43,X44,X45,X46))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(m1_subset_1(k2_partfun1(X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.18/0.40  cnf(c_0_24, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  fof(c_0_27, plain, ![X33, X34, X35, X36]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k7_relset_1(X33,X34,X35,X36)=k9_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.18/0.40  fof(c_0_28, plain, ![X27, X28, X29]:((v4_relat_1(X29,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(v5_relat_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.40  cnf(c_0_29, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.40  cnf(c_0_30, negated_conjecture, (k2_partfun1(esk1_0,esk4_0,esk5_0,X1)=k7_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.18/0.40  fof(c_0_31, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.18/0.40  fof(c_0_32, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.18/0.40  fof(c_0_33, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|(~r1_tarski(k1_relat_1(X39),X37)|~r1_tarski(k2_relat_1(X39),X38)|m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.18/0.40  fof(c_0_34, plain, ![X19, X20]:(~v1_relat_1(X20)|k2_relat_1(k7_relat_1(X20,X19))=k9_relat_1(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.18/0.40  fof(c_0_35, plain, ![X15, X16]:(~v1_relat_1(X15)|v1_relat_1(k7_relat_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.18/0.40  cnf(c_0_36, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.40  fof(c_0_37, plain, ![X21, X22]:(~v1_relat_1(X22)|~v4_relat_1(X22,X21)|X22=k7_relat_1(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.18/0.40  cnf(c_0_38, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.40  cnf(c_0_39, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_30]), c_0_26])])).
% 0.18/0.40  cnf(c_0_40, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.40  cnf(c_0_41, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.18/0.40  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.18/0.40  cnf(c_0_43, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.40  cnf(c_0_44, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk4_0,esk5_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_46, negated_conjecture, (k7_relset_1(esk1_0,esk4_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.18/0.40  cnf(c_0_47, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.40  fof(c_0_48, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.18/0.40  fof(c_0_49, plain, ![X23, X24]:(~v1_relat_1(X24)|r1_tarski(k1_relat_1(k7_relat_1(X24,X23)),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.18/0.40  cnf(c_0_50, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.40  cnf(c_0_51, negated_conjecture, (v4_relat_1(k7_relat_1(esk5_0,X1),esk1_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.40  cnf(c_0_52, negated_conjecture, (v1_relat_1(k7_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_41])])).
% 0.18/0.40  cnf(c_0_53, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X3)|~r1_tarski(k9_relat_1(X1,X2),X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.18/0.40  cnf(c_0_54, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.40  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_25]), c_0_41])])).
% 0.18/0.40  cnf(c_0_56, negated_conjecture, (~v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0))|~v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)|~m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_57, negated_conjecture, (v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_25]), c_0_26])])).
% 0.18/0.40  fof(c_0_58, plain, ![X40, X41, X42]:((((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))))&((~v1_funct_2(X42,X40,X41)|X42=k1_xboole_0|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X42!=k1_xboole_0|v1_funct_2(X42,X40,X41)|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.18/0.40  cnf(c_0_59, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.18/0.40  fof(c_0_60, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.40  fof(c_0_61, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.40  fof(c_0_62, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.40  cnf(c_0_63, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.18/0.40  cnf(c_0_64, negated_conjecture, (k7_relat_1(k7_relat_1(esk5_0,X1),esk1_0)=k7_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.18/0.40  cnf(c_0_65, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~r1_tarski(k1_relat_1(k7_relat_1(esk5_0,esk2_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])])).
% 0.18/0.40  cnf(c_0_66, negated_conjecture, (~v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)|~m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.18/0.40  fof(c_0_67, plain, ![X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(X25,k1_relat_1(X26))|k1_relat_1(k7_relat_1(X26,X25))=X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.18/0.40  cnf(c_0_68, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.40  cnf(c_0_69, negated_conjecture, (k1_relset_1(esk1_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_59, c_0_25])).
% 0.18/0.40  cnf(c_0_70, negated_conjecture, (v1_funct_2(esk5_0,esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.18/0.40  cnf(c_0_72, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.40  cnf(c_0_73, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.40  cnf(c_0_74, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk5_0,X1)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_52])])).
% 0.18/0.40  cnf(c_0_75, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_63]), c_0_55])])).
% 0.18/0.40  cnf(c_0_76, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk2_0),esk2_0,esk3_0)|~m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_30]), c_0_30])).
% 0.18/0.40  cnf(c_0_77, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.18/0.40  cnf(c_0_78, negated_conjecture, (k1_relat_1(esk5_0)=esk1_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_25]), c_0_69]), c_0_70])])).
% 0.18/0.40  cnf(c_0_79, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.18/0.40  cnf(c_0_80, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_73])).
% 0.18/0.40  fof(c_0_81, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.40  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.18/0.40  cnf(c_0_83, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_65, c_0_74])).
% 0.18/0.40  cnf(c_0_84, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.40  cnf(c_0_85, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,k7_relat_1(esk5_0,esk2_0))=k1_relat_1(k7_relat_1(esk5_0,esk2_0))), inference(spm,[status(thm)],[c_0_59, c_0_75])).
% 0.18/0.40  cnf(c_0_86, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk2_0),esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_75])])).
% 0.18/0.40  cnf(c_0_87, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,X1))=X1|esk4_0=k1_xboole_0|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_55])])).
% 0.18/0.40  cnf(c_0_88, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_89, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_38, c_0_79])).
% 0.18/0.40  cnf(c_0_90, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_80])).
% 0.18/0.40  cnf(c_0_91, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.18/0.40  cnf(c_0_92, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.18/0.40  cnf(c_0_93, negated_conjecture, (r1_tarski(k7_relat_1(esk5_0,esk2_0),k2_zfmisc_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.18/0.40  cnf(c_0_94, negated_conjecture, (esk3_0=k1_xboole_0|k1_relat_1(k7_relat_1(esk5_0,esk2_0))!=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_75])]), c_0_86])).
% 0.18/0.40  cnf(c_0_95, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,esk2_0))=esk2_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.18/0.40  cnf(c_0_96, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_89]), c_0_90])])).
% 0.18/0.40  cnf(c_0_97, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_91])).
% 0.18/0.40  cnf(c_0_98, negated_conjecture, (k7_relat_1(esk5_0,esk2_0)=k2_zfmisc_1(esk1_0,esk3_0)|~r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),k7_relat_1(esk5_0,esk2_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.18/0.40  cnf(c_0_99, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.18/0.40  cnf(c_0_100, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_92, c_0_72])).
% 0.18/0.40  cnf(c_0_101, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_96]), c_0_90])])).
% 0.18/0.40  cnf(c_0_102, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_42, c_0_97])).
% 0.18/0.40  cnf(c_0_103, negated_conjecture, (k7_relat_1(esk5_0,esk2_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_80]), c_0_80]), c_0_72])])).
% 0.18/0.40  cnf(c_0_104, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.18/0.40  cnf(c_0_105, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_102, c_0_97])).
% 0.18/0.40  cnf(c_0_106, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.40  cnf(c_0_107, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.40  cnf(c_0_108, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_103]), c_0_104])).
% 0.18/0.40  cnf(c_0_109, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.18/0.40  cnf(c_0_110, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_82, c_0_105])).
% 0.18/0.40  cnf(c_0_111, plain, (k1_relat_1(k7_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_100, c_0_63])).
% 0.18/0.40  cnf(c_0_112, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_106])).
% 0.18/0.40  cnf(c_0_113, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.40  cnf(c_0_114, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])])).
% 0.18/0.40  cnf(c_0_115, plain, (r1_tarski(k7_relat_1(X1,k1_xboole_0),k1_xboole_0)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112]), c_0_44])).
% 0.18/0.40  cnf(c_0_116, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_113]), c_0_112])).
% 0.18/0.40  cnf(c_0_117, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_79]), c_0_104])).
% 0.18/0.40  cnf(c_0_118, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,k1_xboole_0),k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_114]), c_0_114])).
% 0.18/0.40  cnf(c_0_119, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_115]), c_0_72])])).
% 0.18/0.40  cnf(c_0_120, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_79])])).
% 0.18/0.40  cnf(c_0_121, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120]), c_0_55])]), ['proof']).
% 0.18/0.40  # SZS output end CNFRefutation
% 0.18/0.40  # Proof object total steps             : 122
% 0.18/0.40  # Proof object clause steps            : 82
% 0.18/0.40  # Proof object formula steps           : 40
% 0.18/0.40  # Proof object conjectures             : 40
% 0.18/0.40  # Proof object clause conjectures      : 37
% 0.18/0.40  # Proof object formula conjectures     : 3
% 0.18/0.40  # Proof object initial clauses used    : 32
% 0.18/0.40  # Proof object initial formulas used   : 20
% 0.18/0.40  # Proof object generating inferences   : 44
% 0.18/0.40  # Proof object simplifying inferences  : 60
% 0.18/0.40  # Training examples: 0 positive, 0 negative
% 0.18/0.40  # Parsed axioms                        : 20
% 0.18/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.40  # Initial clauses                      : 38
% 0.18/0.40  # Removed in clause preprocessing      : 0
% 0.18/0.40  # Initial clauses in saturation        : 38
% 0.18/0.40  # Processed clauses                    : 553
% 0.18/0.40  # ...of these trivial                  : 8
% 0.18/0.40  # ...subsumed                          : 166
% 0.18/0.40  # ...remaining for further processing  : 379
% 0.18/0.40  # Other redundant clauses eliminated   : 2
% 0.18/0.40  # Clauses deleted for lack of memory   : 0
% 0.18/0.40  # Backward-subsumed                    : 11
% 0.18/0.40  # Backward-rewritten                   : 96
% 0.18/0.40  # Generated clauses                    : 1615
% 0.18/0.40  # ...of the previous two non-trivial   : 1063
% 0.18/0.40  # Contextual simplify-reflections      : 10
% 0.18/0.40  # Paramodulations                      : 1605
% 0.18/0.40  # Factorizations                       : 0
% 0.18/0.40  # Equation resolutions                 : 10
% 0.18/0.40  # Propositional unsat checks           : 0
% 0.18/0.40  #    Propositional check models        : 0
% 0.18/0.40  #    Propositional check unsatisfiable : 0
% 0.18/0.40  #    Propositional clauses             : 0
% 0.18/0.40  #    Propositional clauses after purity: 0
% 0.18/0.40  #    Propositional unsat core size     : 0
% 0.18/0.40  #    Propositional preprocessing time  : 0.000
% 0.18/0.40  #    Propositional encoding time       : 0.000
% 0.18/0.40  #    Propositional solver time         : 0.000
% 0.18/0.40  #    Success case prop preproc time    : 0.000
% 0.18/0.40  #    Success case prop encoding time   : 0.000
% 0.18/0.40  #    Success case prop solver time     : 0.000
% 0.18/0.40  # Current number of processed clauses  : 233
% 0.18/0.40  #    Positive orientable unit clauses  : 85
% 0.18/0.40  #    Positive unorientable unit clauses: 0
% 0.18/0.40  #    Negative unit clauses             : 2
% 0.18/0.40  #    Non-unit-clauses                  : 146
% 0.18/0.40  # Current number of unprocessed clauses: 564
% 0.18/0.40  # ...number of literals in the above   : 1357
% 0.18/0.40  # Current number of archived formulas  : 0
% 0.18/0.40  # Current number of archived clauses   : 144
% 0.18/0.40  # Clause-clause subsumption calls (NU) : 3070
% 0.18/0.40  # Rec. Clause-clause subsumption calls : 2444
% 0.18/0.40  # Non-unit clause-clause subsumptions  : 181
% 0.18/0.40  # Unit Clause-clause subsumption calls : 261
% 0.18/0.40  # Rewrite failures with RHS unbound    : 0
% 0.18/0.40  # BW rewrite match attempts            : 125
% 0.18/0.40  # BW rewrite match successes           : 19
% 0.18/0.40  # Condensation attempts                : 0
% 0.18/0.40  # Condensation successes               : 0
% 0.18/0.40  # Termbank termtop insertions          : 24927
% 0.18/0.40  
% 0.18/0.40  # -------------------------------------------------
% 0.18/0.40  # User time                : 0.064 s
% 0.18/0.40  # System time              : 0.006 s
% 0.18/0.40  # Total time               : 0.070 s
% 0.18/0.40  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
