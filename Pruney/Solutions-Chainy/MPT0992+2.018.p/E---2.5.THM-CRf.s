%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:37 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 803 expanded)
%              Number of clauses        :   78 ( 334 expanded)
%              Number of leaves         :   18 ( 202 expanded)
%              Depth                    :   19
%              Number of atoms          :  340 (3530 expanded)
%              Number of equality atoms :   80 ( 918 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

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

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(t111_relat_1,axiom,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X3,X1)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
              & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
              & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_funct_2])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk3_0,esk1_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
      | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_20,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_22,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_26,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_xboole_0(X26)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_xboole_0(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v1_funct_2(X34,X32,X33)
        | X32 = k1_relset_1(X32,X33,X34)
        | X33 = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_relset_1(X32,X33,X34)
        | v1_funct_2(X34,X32,X33)
        | X33 = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_2(X34,X32,X33)
        | X32 = k1_relset_1(X32,X33,X34)
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_relset_1(X32,X33,X34)
        | v1_funct_2(X34,X32,X33)
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_2(X34,X32,X33)
        | X34 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X34 != k1_xboole_0
        | v1_funct_2(X34,X32,X33)
        | X32 = k1_xboole_0
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ r1_tarski(X18,k1_relat_1(X19))
      | k1_relat_1(k7_relat_1(X19,X18)) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_30,plain,(
    ! [X17] : k7_relat_1(k1_xboole_0,X17) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t111_relat_1])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_40,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_41,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_relset_1(X29,X30,X31) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_42,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_45,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_49,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

fof(c_0_51,plain,(
    ! [X39,X40,X41,X42] :
      ( ~ v1_funct_1(X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_partfun1(X39,X40,X41,X42) = k7_relat_1(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_52,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

fof(c_0_55,plain,(
    ! [X43,X44] :
      ( ( v1_funct_1(X44)
        | ~ r1_tarski(k2_relat_1(X44),X43)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( v1_funct_2(X44,k1_relat_1(X44),X43)
        | ~ r1_tarski(k2_relat_1(X44),X43)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X44),X43)))
        | ~ r1_tarski(k2_relat_1(X44),X43)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_27]),c_0_46])])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relat_1(X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_63,plain,(
    ! [X35,X36,X37,X38] :
      ( ( v1_funct_1(k2_partfun1(X35,X36,X37,X38))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( m1_subset_1(k2_partfun1(X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_56]),c_0_27])])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_27])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,k1_xboole_0,k1_xboole_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_69,plain,
    ( k2_partfun1(X1,X2,k1_xboole_0,X3) = k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_59]),c_0_32])])).

cnf(c_0_70,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_32]),c_0_61])])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_58])).

cnf(c_0_72,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_62]),c_0_66])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_75,plain,
    ( k1_relat_1(k2_partfun1(X1,X2,X3,X4)) = X4
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X4,k1_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_59]),c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_32])]),c_0_71])).

cnf(c_0_77,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_78,plain,
    ( v1_relat_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_59])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[c_0_65,c_0_76])).

cnf(c_0_82,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_77,c_0_59])).

cnf(c_0_83,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_59])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk4_0)))) ),
    inference(sr,[status(thm)],[c_0_79,c_0_76])).

cnf(c_0_85,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_86,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = X1
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_27]),c_0_62]),c_0_81])])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_27]),c_0_62])])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_62])])).

fof(c_0_89,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(k7_relat_1(esk4_0,X1),X1,X2)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_88])])).

cnf(c_0_91,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_92,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_2(k7_relat_1(esk4_0,X1),X1,X2)
    | ~ v5_relat_1(k7_relat_1(esk4_0,X1),X2)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_88])])).

cnf(c_0_94,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(k2_partfun1(X1,X2,esk4_0,X3),X3,X4)
    | ~ v5_relat_1(k2_partfun1(X1,X2,esk4_0,X3),X4)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_59]),c_0_62])])).

cnf(c_0_96,plain,
    ( v5_relat_1(k2_partfun1(X1,X2,X3,X4),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_72])).

fof(c_0_97,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | v1_relat_1(k7_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_98,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k2_partfun1(X5,X6,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_59])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_1(k2_partfun1(X1,X2,esk4_0,X3))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_59]),c_0_62])])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_2(k2_partfun1(X1,X2,esk4_0,X3),X3,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_62])])).

cnf(c_0_101,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(X1,X2,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(X1,X2,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_98]),c_0_62]),c_0_27])]),c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_2(k7_relat_1(esk4_0,X1),X1,X2)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_59]),c_0_62])])).

cnf(c_0_104,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_42]),c_0_101])).

cnf(c_0_105,plain,
    ( v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_59])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_59]),c_0_62])])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_2(k7_relat_1(esk4_0,X1),X1,esk2_0)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_27])).

cnf(c_0_108,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_91]),c_0_101])).

cnf(c_0_109,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_27]),c_0_62])])).

cnf(c_0_110,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_23])])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_87]),c_0_66]),c_0_81])])).

cnf(c_0_112,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_23])])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_27,c_0_112]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.028 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 0.21/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.42  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.21/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.42  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.21/0.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.42  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.21/0.42  fof(t111_relat_1, axiom, ![X1]:k7_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 0.21/0.42  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.21/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.42  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.21/0.42  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.21/0.42  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.21/0.42  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.21/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.42  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.21/0.42  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 0.21/0.42  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk3_0,esk1_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.21/0.42  fof(c_0_20, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.42  fof(c_0_21, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.21/0.42  fof(c_0_22, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.42  cnf(c_0_23, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_24, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  fof(c_0_25, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.42  fof(c_0_26, plain, ![X26, X27, X28]:(~v1_xboole_0(X26)|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_xboole_0(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.21/0.42  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  fof(c_0_28, plain, ![X32, X33, X34]:((((~v1_funct_2(X34,X32,X33)|X32=k1_relset_1(X32,X33,X34)|X33=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X32!=k1_relset_1(X32,X33,X34)|v1_funct_2(X34,X32,X33)|X33=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&((~v1_funct_2(X34,X32,X33)|X32=k1_relset_1(X32,X33,X34)|X32!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X32!=k1_relset_1(X32,X33,X34)|v1_funct_2(X34,X32,X33)|X32!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&((~v1_funct_2(X34,X32,X33)|X34=k1_xboole_0|X32=k1_xboole_0|X33!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X34!=k1_xboole_0|v1_funct_2(X34,X32,X33)|X32=k1_xboole_0|X33!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.42  fof(c_0_29, plain, ![X18, X19]:(~v1_relat_1(X19)|(~r1_tarski(X18,k1_relat_1(X19))|k1_relat_1(k7_relat_1(X19,X18))=X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.21/0.42  fof(c_0_30, plain, ![X17]:k7_relat_1(k1_xboole_0,X17)=k1_xboole_0, inference(variable_rename,[status(thm)],[t111_relat_1])).
% 0.21/0.42  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.42  cnf(c_0_32, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_34, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.42  cnf(c_0_35, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.42  fof(c_0_36, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.21/0.42  cnf(c_0_37, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.21/0.42  cnf(c_0_39, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.42  cnf(c_0_40, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.42  fof(c_0_41, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_relset_1(X29,X30,X31)=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.42  cnf(c_0_42, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.42  cnf(c_0_43, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.42  cnf(c_0_44, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.42  cnf(c_0_45, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.42  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_47, negated_conjecture, (~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_48, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.21/0.42  cnf(c_0_49, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.42  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk4_0)|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.21/0.42  fof(c_0_51, plain, ![X39, X40, X41, X42]:(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k2_partfun1(X39,X40,X41,X42)=k7_relat_1(X41,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.21/0.42  cnf(c_0_52, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_40])).
% 0.21/0.42  cnf(c_0_53, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.42  cnf(c_0_54, plain, (k1_relat_1(k1_xboole_0)=X1|~r1_tarski(X1,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.21/0.42  fof(c_0_55, plain, ![X43, X44]:(((v1_funct_1(X44)|~r1_tarski(k2_relat_1(X44),X43)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(v1_funct_2(X44,k1_relat_1(X44),X43)|~r1_tarski(k2_relat_1(X44),X43)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X44),X43)))|~r1_tarski(k2_relat_1(X44),X43)|(~v1_relat_1(X44)|~v1_funct_1(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.21/0.42  cnf(c_0_56, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_27]), c_0_46])])).
% 0.21/0.42  cnf(c_0_57, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.21/0.42  cnf(c_0_58, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.42  cnf(c_0_59, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.42  cnf(c_0_60, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relat_1(X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.21/0.42  cnf(c_0_61, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_35])).
% 0.21/0.42  cnf(c_0_62, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  fof(c_0_63, plain, ![X35, X36, X37, X38]:((v1_funct_1(k2_partfun1(X35,X36,X37,X38))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(m1_subset_1(k2_partfun1(X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.21/0.42  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.42  cnf(c_0_65, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_56]), c_0_27])])).
% 0.21/0.42  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_27])).
% 0.21/0.42  cnf(c_0_67, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_68, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_1(k2_partfun1(esk1_0,esk2_0,k1_xboole_0,k1_xboole_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.42  cnf(c_0_69, plain, (k2_partfun1(X1,X2,k1_xboole_0,X3)=k1_xboole_0|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_59]), c_0_32])])).
% 0.21/0.42  cnf(c_0_70, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_32]), c_0_61])])).
% 0.21/0.42  cnf(c_0_71, negated_conjecture, (v1_funct_1(k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_62, c_0_58])).
% 0.21/0.42  cnf(c_0_72, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.42  cnf(c_0_73, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_62]), c_0_66])])).
% 0.21/0.42  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_67])).
% 0.21/0.42  cnf(c_0_75, plain, (k1_relat_1(k2_partfun1(X1,X2,X3,X4))=X4|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X4,k1_relat_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_59]), c_0_31])).
% 0.21/0.42  cnf(c_0_76, negated_conjecture, (esk2_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_32])]), c_0_71])).
% 0.21/0.42  cnf(c_0_77, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.21/0.42  cnf(c_0_78, plain, (v1_relat_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_72])).
% 0.21/0.42  cnf(c_0_79, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk4_0))))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.42  cnf(c_0_80, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_59])).
% 0.21/0.42  cnf(c_0_81, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0), inference(sr,[status(thm)],[c_0_65, c_0_76])).
% 0.21/0.42  cnf(c_0_82, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_77, c_0_59])).
% 0.21/0.42  cnf(c_0_83, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_78, c_0_59])).
% 0.21/0.42  cnf(c_0_84, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk4_0))))), inference(sr,[status(thm)],[c_0_79, c_0_76])).
% 0.21/0.42  cnf(c_0_85, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.21/0.42  cnf(c_0_86, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=X1|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_27]), c_0_62]), c_0_81])])).
% 0.21/0.42  cnf(c_0_87, negated_conjecture, (v1_funct_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_27]), c_0_62])])).
% 0.21/0.42  cnf(c_0_88, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_62])])).
% 0.21/0.42  fof(c_0_89, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.21/0.42  cnf(c_0_90, negated_conjecture, (v1_funct_2(k7_relat_1(esk4_0,X1),X1,X2)|~r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),X2)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87]), c_0_88])])).
% 0.21/0.42  cnf(c_0_91, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.21/0.42  fof(c_0_92, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.42  cnf(c_0_93, negated_conjecture, (v1_funct_2(k7_relat_1(esk4_0,X1),X1,X2)|~v5_relat_1(k7_relat_1(esk4_0,X1),X2)|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_88])])).
% 0.21/0.42  cnf(c_0_94, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 0.21/0.42  cnf(c_0_95, negated_conjecture, (v1_funct_2(k2_partfun1(X1,X2,esk4_0,X3),X3,X4)|~v5_relat_1(k2_partfun1(X1,X2,esk4_0,X3),X4)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X3,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_59]), c_0_62])])).
% 0.21/0.42  cnf(c_0_96, plain, (v5_relat_1(k2_partfun1(X1,X2,X3,X4),X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_94, c_0_72])).
% 0.21/0.42  fof(c_0_97, plain, ![X15, X16]:(~v1_relat_1(X15)|v1_relat_1(k7_relat_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.21/0.42  cnf(c_0_98, plain, (k2_partfun1(X1,X2,X3,X4)=k2_partfun1(X5,X6,X3,X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_59, c_0_59])).
% 0.21/0.42  cnf(c_0_99, negated_conjecture, (v1_funct_1(k2_partfun1(X1,X2,esk4_0,X3))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_59]), c_0_62])])).
% 0.21/0.42  cnf(c_0_100, negated_conjecture, (v1_funct_2(k2_partfun1(X1,X2,esk4_0,X3),X3,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X3,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_62])])).
% 0.21/0.42  cnf(c_0_101, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.21/0.42  cnf(c_0_102, negated_conjecture, (~v1_funct_2(k2_partfun1(X1,X2,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(X1,X2,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_98]), c_0_62]), c_0_27])]), c_0_99])).
% 0.21/0.42  cnf(c_0_103, negated_conjecture, (v1_funct_2(k7_relat_1(esk4_0,X1),X1,X2)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_59]), c_0_62])])).
% 0.21/0.42  cnf(c_0_104, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_42]), c_0_101])).
% 0.21/0.42  cnf(c_0_105, plain, (v5_relat_1(k7_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_96, c_0_59])).
% 0.21/0.42  cnf(c_0_106, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_59]), c_0_62])])).
% 0.21/0.42  cnf(c_0_107, negated_conjecture, (v1_funct_2(k7_relat_1(esk4_0,X1),X1,esk2_0)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_103, c_0_27])).
% 0.21/0.42  cnf(c_0_108, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(k7_relat_1(X1,X2))|~v5_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_91]), c_0_101])).
% 0.21/0.42  cnf(c_0_109, negated_conjecture, (v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_27]), c_0_62])])).
% 0.21/0.42  cnf(c_0_110, negated_conjecture, (~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_23])])).
% 0.21/0.42  cnf(c_0_111, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_87]), c_0_66]), c_0_81])])).
% 0.21/0.42  cnf(c_0_112, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_23])])).
% 0.21/0.42  cnf(c_0_113, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_27, c_0_112]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 114
% 0.21/0.42  # Proof object clause steps            : 78
% 0.21/0.42  # Proof object formula steps           : 36
% 0.21/0.42  # Proof object conjectures             : 42
% 0.21/0.42  # Proof object clause conjectures      : 39
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 27
% 0.21/0.42  # Proof object initial formulas used   : 18
% 0.21/0.42  # Proof object generating inferences   : 46
% 0.21/0.42  # Proof object simplifying inferences  : 65
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 19
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 36
% 0.21/0.42  # Removed in clause preprocessing      : 1
% 0.21/0.42  # Initial clauses in saturation        : 35
% 0.21/0.42  # Processed clauses                    : 760
% 0.21/0.42  # ...of these trivial                  : 17
% 0.21/0.42  # ...subsumed                          : 415
% 0.21/0.42  # ...remaining for further processing  : 328
% 0.21/0.42  # Other redundant clauses eliminated   : 9
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 27
% 0.21/0.42  # Backward-rewritten                   : 15
% 0.21/0.42  # Generated clauses                    : 1641
% 0.21/0.42  # ...of the previous two non-trivial   : 1139
% 0.21/0.42  # Contextual simplify-reflections      : 33
% 0.21/0.42  # Paramodulations                      : 1624
% 0.21/0.42  # Factorizations                       : 2
% 0.21/0.42  # Equation resolutions                 : 9
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 239
% 0.21/0.42  #    Positive orientable unit clauses  : 30
% 0.21/0.42  #    Positive unorientable unit clauses: 0
% 0.21/0.42  #    Negative unit clauses             : 4
% 0.21/0.42  #    Non-unit-clauses                  : 205
% 0.21/0.42  # Current number of unprocessed clauses: 394
% 0.21/0.42  # ...number of literals in the above   : 1588
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 83
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 6004
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 3255
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 305
% 0.21/0.42  # Unit Clause-clause subsumption calls : 328
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 27
% 0.21/0.42  # BW rewrite match successes           : 11
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 31110
% 0.21/0.43  
% 0.21/0.43  # -------------------------------------------------
% 0.21/0.43  # User time                : 0.077 s
% 0.21/0.43  # System time              : 0.002 s
% 0.21/0.43  # Total time               : 0.079 s
% 0.21/0.43  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
