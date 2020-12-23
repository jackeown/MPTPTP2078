%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:38 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  120 (1373 expanded)
%              Number of clauses        :   87 ( 595 expanded)
%              Number of leaves         :   16 ( 344 expanded)
%              Depth                    :   17
%              Number of atoms          :  358 (5300 expanded)
%              Number of equality atoms :   89 (1313 expanded)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

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

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_18,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_19,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & r1_tarski(esk4_0,esk2_0)
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))
      | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_23,plain,(
    ! [X14,X15] :
      ( ( k2_zfmisc_1(X14,X15) != k1_xboole_0
        | X14 = k1_xboole_0
        | X15 = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X14,X15) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k7_relat_1(X23,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X18,X19] :
      ( ( ~ v5_relat_1(X19,X18)
        | r1_tarski(k2_relat_1(X19),X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(k2_relat_1(X19),X18)
        | v5_relat_1(X19,X18)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_30,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(k2_partfun1(X38,X39,X40,X41))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(k2_partfun1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_36,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k2_partfun1(X42,X43,X44,X45) = k7_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_37,plain,(
    ! [X46,X47] :
      ( ( v1_funct_1(X47)
        | ~ r1_tarski(k2_relat_1(X47),X46)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( v1_funct_2(X47,k1_relat_1(X47),X46)
        | ~ r1_tarski(k2_relat_1(X47),X46)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X47),X46)))
        | ~ r1_tarski(k2_relat_1(X47),X46)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_38,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(X24,k1_relat_1(X25))
      | k1_relat_1(k7_relat_1(X25,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_39,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | v1_relat_1(k7_relat_1(X20,X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_41,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))
    | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_55,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_56,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_57,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_59,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_60,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_43])).

cnf(c_0_61,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk5_0,k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

fof(c_0_64,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X37 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != k1_xboole_0
        | v1_funct_2(X37,X35,X36)
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_33])])).

cnf(c_0_66,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k2_partfun1(X5,X6,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_53])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_partfun1(X1,X2,X3,X4),k2_zfmisc_1(X1,X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_54])).

cnf(c_0_68,plain,
    ( v1_funct_2(k7_relat_1(X1,X2),X2,X3)
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_69,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59])])).

cnf(c_0_70,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_62]),c_0_59])])).

cnf(c_0_71,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_63]),c_0_25])])).

fof(c_0_72,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_73,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(X1,X2,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(X1,X2,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_52]),c_0_33])])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_partfun1(k1_xboole_0,X1,X2,X3),k1_xboole_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_49])).

cnf(c_0_77,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_59]),c_0_70]),c_0_25])])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_71])).

cnf(c_0_79,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_69]),c_0_59])])).

cnf(c_0_80,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_33]),c_0_74])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(X1,X2,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_partfun1(X1,X2,esk5_0,esk4_0),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_28])).

cnf(c_0_83,plain,
    ( k2_partfun1(k1_xboole_0,X1,X2,X3) = k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_76]),c_0_25])])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(X1,k1_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_25])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_33])])).

cnf(c_0_89,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_33])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk4_0,esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_49]),c_0_25]),c_0_52])])).

cnf(c_0_91,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_86,c_0_48])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_48]),c_0_49])).

cnf(c_0_94,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_52]),c_0_89])])).

cnf(c_0_95,plain,
    ( k1_relat_1(k2_partfun1(X1,X2,X3,X4)) = X4
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X4,k1_relat_1(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_27])).

cnf(c_0_96,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_93])).

cnf(c_0_97,plain,
    ( v1_relat_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_53]),c_0_27])).

cnf(c_0_98,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_45])).

cnf(c_0_99,plain,
    ( v5_relat_1(k2_partfun1(X1,X2,X3,X4),X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_54])).

cnf(c_0_100,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_53])).

cnf(c_0_101,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0 ),
    inference(sr,[status(thm)],[c_0_88,c_0_96])).

cnf(c_0_102,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_53])).

cnf(c_0_103,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_97,c_0_53])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(esk5_0)))) ),
    inference(sr,[status(thm)],[c_0_98,c_0_96])).

cnf(c_0_105,plain,
    ( v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_53])).

cnf(c_0_106,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_87])).

cnf(c_0_107,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,X1)) = X1
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_33]),c_0_52]),c_0_101])])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_33]),c_0_52])])).

cnf(c_0_109,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_52])])).

cnf(c_0_110,plain,
    ( v1_funct_2(k7_relat_1(X1,X2),X2,X3)
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_57])).

cnf(c_0_111,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk5_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_33]),c_0_52])])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk5_0,X1)),X2)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_108]),c_0_109])])).

cnf(c_0_113,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k7_relat_1(esk5_0,esk4_0),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_53]),c_0_52])])).

cnf(c_0_114,negated_conjecture,
    ( v1_funct_2(k7_relat_1(esk5_0,X1),X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_108]),c_0_89]),c_0_101])])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(X1,X2))
    | ~ v5_relat_1(k7_relat_1(esk5_0,X1),X2)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_43]),c_0_109])])).

cnf(c_0_116,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k7_relat_1(esk5_0,esk4_0),k2_zfmisc_1(esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_86])])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(X1,esk3_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_111])).

cnf(c_0_118,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_86])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_33,c_0_118]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.53  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05AN
% 0.37/0.53  # and selection function PSelectComplexExceptUniqMaxPosHorn.
% 0.37/0.53  #
% 0.37/0.53  # Preprocessing time       : 0.028 s
% 0.37/0.53  # Presaturation interreduction done
% 0.37/0.53  
% 0.37/0.53  # Proof found!
% 0.37/0.53  # SZS status Theorem
% 0.37/0.53  # SZS output start CNFRefutation
% 0.37/0.53  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 0.37/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.37/0.53  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.37/0.53  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.37/0.54  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.37/0.54  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.37/0.54  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.37/0.54  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 0.37/0.54  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.37/0.54  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.37/0.54  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.37/0.54  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.37/0.54  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.37/0.54  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.37/0.54  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.37/0.54  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.37/0.54  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 0.37/0.54  fof(c_0_17, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.37/0.54  fof(c_0_18, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.37/0.54  fof(c_0_19, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.37/0.54  fof(c_0_20, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.37/0.54  fof(c_0_21, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.37/0.54  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r1_tarski(esk4_0,esk2_0)&((esk3_0!=k1_xboole_0|esk2_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.37/0.54  fof(c_0_23, plain, ![X14, X15]:((k2_zfmisc_1(X14,X15)!=k1_xboole_0|(X14=k1_xboole_0|X15=k1_xboole_0))&((X14!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0)&(X15!=k1_xboole_0|k2_zfmisc_1(X14,X15)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.37/0.54  cnf(c_0_24, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.54  cnf(c_0_25, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.37/0.54  fof(c_0_26, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k7_relat_1(X23,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.37/0.54  cnf(c_0_27, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.54  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.54  fof(c_0_29, plain, ![X18, X19]:((~v5_relat_1(X19,X18)|r1_tarski(k2_relat_1(X19),X18)|~v1_relat_1(X19))&(~r1_tarski(k2_relat_1(X19),X18)|v5_relat_1(X19,X18)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.37/0.54  cnf(c_0_30, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.37/0.54  cnf(c_0_31, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.37/0.54  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.37/0.54  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.54  cnf(c_0_34, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.54  fof(c_0_35, plain, ![X38, X39, X40, X41]:((v1_funct_1(k2_partfun1(X38,X39,X40,X41))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(m1_subset_1(k2_partfun1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.37/0.54  fof(c_0_36, plain, ![X42, X43, X44, X45]:(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k2_partfun1(X42,X43,X44,X45)=k7_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.37/0.54  fof(c_0_37, plain, ![X46, X47]:(((v1_funct_1(X47)|~r1_tarski(k2_relat_1(X47),X46)|(~v1_relat_1(X47)|~v1_funct_1(X47)))&(v1_funct_2(X47,k1_relat_1(X47),X46)|~r1_tarski(k2_relat_1(X47),X46)|(~v1_relat_1(X47)|~v1_funct_1(X47))))&(m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X47),X46)))|~r1_tarski(k2_relat_1(X47),X46)|(~v1_relat_1(X47)|~v1_funct_1(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.37/0.54  fof(c_0_38, plain, ![X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(X24,k1_relat_1(X25))|k1_relat_1(k7_relat_1(X25,X24))=X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.37/0.54  fof(c_0_39, plain, ![X20, X21]:(~v1_relat_1(X20)|v1_relat_1(k7_relat_1(X20,X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.37/0.54  cnf(c_0_40, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.37/0.54  cnf(c_0_41, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.37/0.54  cnf(c_0_42, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.37/0.54  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.37/0.54  cnf(c_0_44, plain, (v5_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_30, c_0_28])).
% 0.37/0.54  cnf(c_0_45, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_31])).
% 0.37/0.54  cnf(c_0_46, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.54  cnf(c_0_47, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.37/0.54  cnf(c_0_48, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.54  cnf(c_0_49, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_34])).
% 0.37/0.54  cnf(c_0_50, negated_conjecture, (~v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.54  cnf(c_0_51, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.37/0.54  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.54  cnf(c_0_53, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.37/0.54  cnf(c_0_54, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.37/0.54  cnf(c_0_55, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.54  cnf(c_0_56, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.37/0.54  cnf(c_0_57, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.37/0.54  cnf(c_0_58, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.37/0.54  cnf(c_0_59, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.37/0.54  cnf(c_0_60, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_43])).
% 0.37/0.54  cnf(c_0_61, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.37/0.54  cnf(c_0_62, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_46])).
% 0.37/0.54  cnf(c_0_63, negated_conjecture, (r1_tarski(esk5_0,k1_xboole_0)|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.37/0.54  fof(c_0_64, plain, ![X35, X36, X37]:((((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))))&((~v1_funct_2(X37,X35,X36)|X37=k1_xboole_0|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X37!=k1_xboole_0|v1_funct_2(X37,X35,X36)|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.37/0.54  cnf(c_0_65, negated_conjecture, (~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_33])])).
% 0.37/0.54  cnf(c_0_66, plain, (k2_partfun1(X1,X2,X3,X4)=k2_partfun1(X5,X6,X3,X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_53, c_0_53])).
% 0.37/0.54  cnf(c_0_67, plain, (r1_tarski(k2_partfun1(X1,X2,X3,X4),k2_zfmisc_1(X1,X2))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_32, c_0_54])).
% 0.37/0.54  cnf(c_0_68, plain, (v1_funct_2(k7_relat_1(X1,X2),X2,X3)|~v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.37/0.54  cnf(c_0_69, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59])])).
% 0.37/0.54  cnf(c_0_70, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_62]), c_0_59])])).
% 0.37/0.54  cnf(c_0_71, negated_conjecture, (esk5_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_63]), c_0_25])])).
% 0.37/0.54  fof(c_0_72, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.37/0.54  cnf(c_0_73, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.37/0.54  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.54  cnf(c_0_75, negated_conjecture, (~v1_funct_2(k2_partfun1(X1,X2,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(X1,X2,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_52]), c_0_33])])).
% 0.37/0.54  cnf(c_0_76, plain, (r1_tarski(k2_partfun1(k1_xboole_0,X1,X2,X3),k1_xboole_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_67, c_0_49])).
% 0.37/0.54  cnf(c_0_77, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_funct_1(k1_xboole_0)|~r1_tarski(X1,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_59]), c_0_70]), c_0_25])])).
% 0.37/0.54  cnf(c_0_78, negated_conjecture, (v1_funct_1(k1_xboole_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_71])).
% 0.37/0.54  cnf(c_0_79, plain, (k1_relat_1(k1_xboole_0)=X1|~r1_tarski(X1,k1_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_69]), c_0_59])])).
% 0.37/0.54  cnf(c_0_80, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.37/0.54  cnf(c_0_81, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk5_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_33]), c_0_74])])).
% 0.37/0.54  cnf(c_0_82, negated_conjecture, (~v1_funct_2(k2_partfun1(X1,X2,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k2_partfun1(X1,X2,esk5_0,esk4_0),k2_zfmisc_1(esk4_0,esk3_0))), inference(spm,[status(thm)],[c_0_75, c_0_28])).
% 0.37/0.54  cnf(c_0_83, plain, (k2_partfun1(k1_xboole_0,X1,X2,X3)=k1_xboole_0|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_76]), c_0_25])])).
% 0.37/0.54  cnf(c_0_84, negated_conjecture, (v1_funct_2(k1_xboole_0,X1,X2)|esk3_0!=k1_xboole_0|~r1_tarski(X1,k1_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.37/0.54  cnf(c_0_85, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_79, c_0_25])).
% 0.37/0.54  cnf(c_0_86, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.37/0.54  cnf(c_0_87, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.54  cnf(c_0_88, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_33])])).
% 0.37/0.54  cnf(c_0_89, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_33])).
% 0.37/0.54  cnf(c_0_90, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk4_0,esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_49]), c_0_25]), c_0_52])])).
% 0.37/0.54  cnf(c_0_91, negated_conjecture, (v1_funct_2(k1_xboole_0,X1,X2)|esk3_0!=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(rw,[status(thm)],[c_0_84, c_0_85])).
% 0.37/0.54  cnf(c_0_92, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_86, c_0_48])).
% 0.37/0.54  cnf(c_0_93, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_48]), c_0_49])).
% 0.37/0.54  cnf(c_0_94, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~r1_tarski(k2_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_52]), c_0_89])])).
% 0.37/0.54  cnf(c_0_95, plain, (k1_relat_1(k2_partfun1(X1,X2,X3,X4))=X4|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X4,k1_relat_1(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_53]), c_0_27])).
% 0.37/0.54  cnf(c_0_96, negated_conjecture, (esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_93])).
% 0.37/0.54  cnf(c_0_97, plain, (v1_relat_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_53]), c_0_27])).
% 0.37/0.54  cnf(c_0_98, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(esk5_0))))), inference(spm,[status(thm)],[c_0_94, c_0_45])).
% 0.37/0.54  cnf(c_0_99, plain, (v5_relat_1(k2_partfun1(X1,X2,X3,X4),X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_54])).
% 0.37/0.54  cnf(c_0_100, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_95, c_0_53])).
% 0.37/0.54  cnf(c_0_101, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0), inference(sr,[status(thm)],[c_0_88, c_0_96])).
% 0.37/0.54  cnf(c_0_102, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_51, c_0_53])).
% 0.37/0.54  cnf(c_0_103, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_97, c_0_53])).
% 0.37/0.54  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(esk5_0))))), inference(sr,[status(thm)],[c_0_98, c_0_96])).
% 0.37/0.54  cnf(c_0_105, plain, (v5_relat_1(k7_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_99, c_0_53])).
% 0.37/0.54  cnf(c_0_106, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),X2))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_32, c_0_87])).
% 0.37/0.54  cnf(c_0_107, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,X1))=X1|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_33]), c_0_52]), c_0_101])])).
% 0.37/0.54  cnf(c_0_108, negated_conjecture, (v1_funct_1(k7_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_33]), c_0_52])])).
% 0.37/0.54  cnf(c_0_109, negated_conjecture, (v1_relat_1(k7_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_52])])).
% 0.37/0.54  cnf(c_0_110, plain, (v1_funct_2(k7_relat_1(X1,X2),X2,X3)|~v1_funct_1(k7_relat_1(X1,X2))|~v5_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_43]), c_0_57])).
% 0.37/0.54  cnf(c_0_111, negated_conjecture, (v5_relat_1(k7_relat_1(esk5_0,X1),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_33]), c_0_52])])).
% 0.37/0.54  cnf(c_0_112, negated_conjecture, (r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(X1,X2))|~r1_tarski(k2_relat_1(k7_relat_1(esk5_0,X1)),X2)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_108]), c_0_109])])).
% 0.37/0.54  cnf(c_0_113, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k7_relat_1(esk5_0,esk4_0),k2_zfmisc_1(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_53]), c_0_52])])).
% 0.37/0.54  cnf(c_0_114, negated_conjecture, (v1_funct_2(k7_relat_1(esk5_0,X1),X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_108]), c_0_89]), c_0_101])])).
% 0.37/0.54  cnf(c_0_115, negated_conjecture, (r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(X1,X2))|~v5_relat_1(k7_relat_1(esk5_0,X1),X2)|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_43]), c_0_109])])).
% 0.37/0.54  cnf(c_0_116, negated_conjecture, (~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k7_relat_1(esk5_0,esk4_0),k2_zfmisc_1(esk4_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_114]), c_0_86])])).
% 0.37/0.54  cnf(c_0_117, negated_conjecture, (r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(X1,esk3_0))|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_115, c_0_111])).
% 0.37/0.54  cnf(c_0_118, negated_conjecture, (~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_86])])).
% 0.37/0.54  cnf(c_0_119, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_33, c_0_118]), ['proof']).
% 0.37/0.54  # SZS output end CNFRefutation
% 0.37/0.54  # Proof object total steps             : 120
% 0.37/0.54  # Proof object clause steps            : 87
% 0.37/0.54  # Proof object formula steps           : 33
% 0.37/0.54  # Proof object conjectures             : 41
% 0.37/0.54  # Proof object clause conjectures      : 38
% 0.37/0.54  # Proof object formula conjectures     : 3
% 0.37/0.54  # Proof object initial clauses used    : 26
% 0.37/0.54  # Proof object initial formulas used   : 16
% 0.37/0.54  # Proof object generating inferences   : 53
% 0.37/0.54  # Proof object simplifying inferences  : 72
% 0.37/0.54  # Training examples: 0 positive, 0 negative
% 0.37/0.54  # Parsed axioms                        : 17
% 0.37/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.54  # Initial clauses                      : 39
% 0.37/0.54  # Removed in clause preprocessing      : 1
% 0.37/0.54  # Initial clauses in saturation        : 38
% 0.37/0.54  # Processed clauses                    : 2323
% 0.37/0.54  # ...of these trivial                  : 28
% 0.37/0.54  # ...subsumed                          : 1569
% 0.37/0.54  # ...remaining for further processing  : 726
% 0.37/0.54  # Other redundant clauses eliminated   : 15
% 0.37/0.54  # Clauses deleted for lack of memory   : 0
% 0.37/0.54  # Backward-subsumed                    : 100
% 0.37/0.54  # Backward-rewritten                   : 32
% 0.37/0.54  # Generated clauses                    : 6195
% 0.37/0.54  # ...of the previous two non-trivial   : 3834
% 0.37/0.54  # Contextual simplify-reflections      : 104
% 0.37/0.54  # Paramodulations                      : 6156
% 0.37/0.54  # Factorizations                       : 16
% 0.37/0.54  # Equation resolutions                 : 15
% 0.37/0.54  # Propositional unsat checks           : 0
% 0.37/0.54  #    Propositional check models        : 0
% 0.37/0.54  #    Propositional check unsatisfiable : 0
% 0.37/0.54  #    Propositional clauses             : 0
% 0.37/0.54  #    Propositional clauses after purity: 0
% 0.37/0.54  #    Propositional unsat core size     : 0
% 0.37/0.54  #    Propositional preprocessing time  : 0.000
% 0.37/0.54  #    Propositional encoding time       : 0.000
% 0.37/0.54  #    Propositional solver time         : 0.000
% 0.37/0.54  #    Success case prop preproc time    : 0.000
% 0.37/0.54  #    Success case prop encoding time   : 0.000
% 0.37/0.54  #    Success case prop solver time     : 0.000
% 0.37/0.54  # Current number of processed clauses  : 540
% 0.37/0.54  #    Positive orientable unit clauses  : 58
% 0.37/0.54  #    Positive unorientable unit clauses: 0
% 0.37/0.54  #    Negative unit clauses             : 4
% 0.37/0.54  #    Non-unit-clauses                  : 478
% 0.37/0.54  # Current number of unprocessed clauses: 1512
% 0.37/0.54  # ...number of literals in the above   : 7179
% 0.37/0.54  # Current number of archived formulas  : 0
% 0.37/0.54  # Current number of archived clauses   : 178
% 0.37/0.54  # Clause-clause subsumption calls (NU) : 51331
% 0.37/0.54  # Rec. Clause-clause subsumption calls : 26160
% 0.37/0.54  # Non-unit clause-clause subsumptions  : 1228
% 0.37/0.54  # Unit Clause-clause subsumption calls : 1369
% 0.37/0.54  # Rewrite failures with RHS unbound    : 0
% 0.37/0.54  # BW rewrite match attempts            : 41
% 0.37/0.54  # BW rewrite match successes           : 18
% 0.37/0.54  # Condensation attempts                : 0
% 0.37/0.54  # Condensation successes               : 0
% 0.37/0.54  # Termbank termtop insertions          : 103424
% 0.37/0.54  
% 0.37/0.54  # -------------------------------------------------
% 0.37/0.54  # User time                : 0.183 s
% 0.37/0.54  # System time              : 0.008 s
% 0.37/0.54  # Total time               : 0.192 s
% 0.37/0.54  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
