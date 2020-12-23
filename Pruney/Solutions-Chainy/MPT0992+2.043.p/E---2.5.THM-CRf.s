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
% DateTime   : Thu Dec  3 11:03:40 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 552 expanded)
%              Number of clauses        :   65 ( 230 expanded)
%              Number of leaves         :   16 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  294 (2506 expanded)
%              Number of equality atoms :   88 ( 685 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

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

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk3_0,esk1_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
      | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_18,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(k2_partfun1(X38,X39,X40,X41))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(k2_partfun1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_xboole_0)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_27,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_22,c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_35,c_0_32])).

fof(c_0_43,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | r1_tarski(k7_relat_1(X20,X19),X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_44,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_47,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k2_partfun1(X42,X43,X44,X45) = k7_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_22])).

cnf(c_0_51,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_25])).

cnf(c_0_54,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_25])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_58,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

fof(c_0_60,plain,(
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

fof(c_0_61,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_relset_1(X29,X30,X31) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_63,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_46]),c_0_25])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_31])).

fof(c_0_67,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_68,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_59])).

cnf(c_0_70,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k2_partfun1(X5,X6,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_54])).

cnf(c_0_71,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_73,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ r1_tarski(X21,k1_relat_1(X22))
      | k1_relat_1(k7_relat_1(X22,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_74,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_38])).

fof(c_0_77,plain,(
    ! [X32,X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ r1_tarski(k1_relat_1(X34),X32)
      | ~ r1_tarski(k2_relat_1(X34),X33)
      | m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_78,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_79,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_80,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(X1,X2,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(X1,X2,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_70]),c_0_21]),c_0_22])])).

cnf(c_0_82,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relat_1(X2) != X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_84,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_34]),c_0_76])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])])).

fof(c_0_88,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | r1_tarski(k1_relat_1(k7_relat_1(X18,X17)),X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_54]),c_0_21])])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(X2,X3),X3,X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(X3,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_49]),c_0_22])]),c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_80])])).

cnf(c_0_93,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_52]),c_0_91]),c_0_24])]),c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_52])])).

cnf(c_0_96,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_22,c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.49/0.68  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.49/0.68  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.49/0.68  #
% 0.49/0.68  # Preprocessing time       : 0.028 s
% 0.49/0.68  # Presaturation interreduction done
% 0.49/0.68  
% 0.49/0.68  # Proof found!
% 0.49/0.68  # SZS status Theorem
% 0.49/0.68  # SZS output start CNFRefutation
% 0.49/0.68  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 0.49/0.68  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.49/0.68  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.49/0.68  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.49/0.68  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.49/0.68  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.49/0.68  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.49/0.68  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.49/0.68  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.49/0.68  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.49/0.68  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.49/0.68  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.49/0.68  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.49/0.68  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.49/0.68  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.49/0.68  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.49/0.68  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 0.49/0.68  fof(c_0_17, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk3_0,esk1_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.49/0.68  fof(c_0_18, plain, ![X38, X39, X40, X41]:((v1_funct_1(k2_partfun1(X38,X39,X40,X41))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(m1_subset_1(k2_partfun1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.49/0.68  cnf(c_0_19, negated_conjecture, (~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.68  cnf(c_0_20, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.49/0.68  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.68  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.68  fof(c_0_23, plain, ![X8]:(~r1_tarski(X8,k1_xboole_0)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.49/0.68  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.68  cnf(c_0_25, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.68  fof(c_0_26, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.49/0.68  fof(c_0_27, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.49/0.68  fof(c_0_28, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.49/0.68  cnf(c_0_29, negated_conjecture, (~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])])).
% 0.49/0.68  cnf(c_0_30, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.49/0.68  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.49/0.68  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.49/0.68  cnf(c_0_33, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.49/0.68  cnf(c_0_34, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.49/0.68  cnf(c_0_35, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.49/0.68  fof(c_0_36, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.49/0.68  cnf(c_0_37, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.49/0.68  cnf(c_0_38, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.49/0.68  cnf(c_0_39, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_30, c_0_32])).
% 0.49/0.68  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_33])).
% 0.49/0.68  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_22, c_0_34])).
% 0.49/0.68  cnf(c_0_42, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_35, c_0_32])).
% 0.49/0.68  fof(c_0_43, plain, ![X19, X20]:(~v1_relat_1(X20)|r1_tarski(k7_relat_1(X20,X19),X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.49/0.68  cnf(c_0_44, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.49/0.68  cnf(c_0_45, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.49/0.68  cnf(c_0_46, negated_conjecture, (esk4_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.49/0.68  fof(c_0_47, plain, ![X42, X43, X44, X45]:(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k2_partfun1(X42,X43,X44,X45)=k7_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.49/0.68  cnf(c_0_48, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_41])).
% 0.49/0.68  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.49/0.68  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_22])).
% 0.49/0.68  cnf(c_0_51, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.49/0.68  cnf(c_0_52, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_22])).
% 0.49/0.68  cnf(c_0_53, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_25])).
% 0.49/0.68  cnf(c_0_54, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.49/0.68  cnf(c_0_55, negated_conjecture, (v1_funct_1(k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_48])).
% 0.49/0.68  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_25])).
% 0.49/0.68  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.49/0.68  fof(c_0_58, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.49/0.68  cnf(c_0_59, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.49/0.68  fof(c_0_60, plain, ![X35, X36, X37]:((((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))))&((~v1_funct_2(X37,X35,X36)|X37=k1_xboole_0|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X37!=k1_xboole_0|v1_funct_2(X37,X35,X36)|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.49/0.68  fof(c_0_61, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_relset_1(X29,X30,X31)=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.49/0.68  cnf(c_0_62, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.49/0.68  cnf(c_0_63, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_51])).
% 0.49/0.68  cnf(c_0_64, negated_conjecture, (v1_relat_1(k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_48])).
% 0.49/0.68  cnf(c_0_65, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_46]), c_0_25])).
% 0.49/0.68  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_31])).
% 0.49/0.68  fof(c_0_67, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.49/0.68  cnf(c_0_68, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.49/0.68  cnf(c_0_69, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_57, c_0_59])).
% 0.49/0.68  cnf(c_0_70, plain, (k2_partfun1(X1,X2,X3,X4)=k2_partfun1(X5,X6,X3,X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_54, c_0_54])).
% 0.49/0.68  cnf(c_0_71, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.49/0.68  cnf(c_0_72, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.49/0.68  fof(c_0_73, plain, ![X21, X22]:(~v1_relat_1(X22)|(~r1_tarski(X21,k1_relat_1(X22))|k1_relat_1(k7_relat_1(X22,X21))=X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.49/0.68  cnf(c_0_74, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.49/0.68  cnf(c_0_75, negated_conjecture, (esk2_0!=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65])).
% 0.49/0.68  cnf(c_0_76, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_38])).
% 0.49/0.68  fof(c_0_77, plain, ![X32, X33, X34]:(~v1_relat_1(X34)|(~r1_tarski(k1_relat_1(X34),X32)|~r1_tarski(k2_relat_1(X34),X33)|m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.49/0.68  cnf(c_0_78, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.49/0.68  cnf(c_0_79, negated_conjecture, (v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.49/0.68  cnf(c_0_80, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(spm,[status(thm)],[c_0_44, c_0_69])).
% 0.49/0.68  cnf(c_0_81, negated_conjecture, (~v1_funct_2(k2_partfun1(X1,X2,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(X1,X2,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_70]), c_0_21]), c_0_22])])).
% 0.49/0.68  cnf(c_0_82, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relat_1(X2)!=X3|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.49/0.68  cnf(c_0_83, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.49/0.68  cnf(c_0_84, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_72, c_0_74])).
% 0.49/0.68  cnf(c_0_85, negated_conjecture, (esk2_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_34]), c_0_76])).
% 0.49/0.68  cnf(c_0_86, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.49/0.68  cnf(c_0_87, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])])).
% 0.49/0.68  fof(c_0_88, plain, ![X17, X18]:(~v1_relat_1(X18)|r1_tarski(k1_relat_1(k7_relat_1(X18,X17)),X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.49/0.68  cnf(c_0_89, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_54]), c_0_21])])).
% 0.49/0.68  cnf(c_0_90, plain, (X1=k1_xboole_0|v1_funct_2(k7_relat_1(X2,X3),X3,X1)|~v1_relat_1(X2)|~m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(X3,k1_relat_1(X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83])])).
% 0.49/0.68  cnf(c_0_91, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_49]), c_0_22])]), c_0_85])).
% 0.49/0.68  cnf(c_0_92, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_80])])).
% 0.49/0.68  cnf(c_0_93, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.49/0.68  cnf(c_0_94, negated_conjecture, (~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_52]), c_0_91]), c_0_24])]), c_0_85])).
% 0.49/0.68  cnf(c_0_95, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_52])])).
% 0.49/0.68  cnf(c_0_96, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 0.49/0.68  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_22, c_0_96]), ['proof']).
% 0.49/0.68  # SZS output end CNFRefutation
% 0.49/0.68  # Proof object total steps             : 98
% 0.49/0.68  # Proof object clause steps            : 65
% 0.49/0.68  # Proof object formula steps           : 33
% 0.49/0.68  # Proof object conjectures             : 43
% 0.49/0.68  # Proof object clause conjectures      : 40
% 0.49/0.68  # Proof object formula conjectures     : 3
% 0.49/0.68  # Proof object initial clauses used    : 24
% 0.49/0.68  # Proof object initial formulas used   : 16
% 0.49/0.68  # Proof object generating inferences   : 39
% 0.49/0.68  # Proof object simplifying inferences  : 34
% 0.49/0.68  # Training examples: 0 positive, 0 negative
% 0.49/0.68  # Parsed axioms                        : 17
% 0.49/0.68  # Removed by relevancy pruning/SinE    : 0
% 0.49/0.68  # Initial clauses                      : 33
% 0.49/0.68  # Removed in clause preprocessing      : 0
% 0.49/0.68  # Initial clauses in saturation        : 33
% 0.49/0.68  # Processed clauses                    : 5090
% 0.49/0.68  # ...of these trivial                  : 55
% 0.49/0.68  # ...subsumed                          : 4263
% 0.49/0.68  # ...remaining for further processing  : 772
% 0.49/0.68  # Other redundant clauses eliminated   : 6
% 0.49/0.68  # Clauses deleted for lack of memory   : 0
% 0.49/0.68  # Backward-subsumed                    : 60
% 0.49/0.68  # Backward-rewritten                   : 68
% 0.49/0.68  # Generated clauses                    : 15598
% 0.49/0.68  # ...of the previous two non-trivial   : 12842
% 0.49/0.68  # Contextual simplify-reflections      : 52
% 0.49/0.68  # Paramodulations                      : 15574
% 0.49/0.68  # Factorizations                       : 0
% 0.49/0.68  # Equation resolutions                 : 23
% 0.49/0.68  # Propositional unsat checks           : 0
% 0.49/0.68  #    Propositional check models        : 0
% 0.49/0.68  #    Propositional check unsatisfiable : 0
% 0.49/0.68  #    Propositional clauses             : 0
% 0.49/0.68  #    Propositional clauses after purity: 0
% 0.49/0.68  #    Propositional unsat core size     : 0
% 0.49/0.68  #    Propositional preprocessing time  : 0.000
% 0.49/0.68  #    Propositional encoding time       : 0.000
% 0.49/0.68  #    Propositional solver time         : 0.000
% 0.49/0.68  #    Success case prop preproc time    : 0.000
% 0.49/0.68  #    Success case prop encoding time   : 0.000
% 0.49/0.68  #    Success case prop solver time     : 0.000
% 0.49/0.68  # Current number of processed clauses  : 610
% 0.49/0.68  #    Positive orientable unit clauses  : 69
% 0.49/0.68  #    Positive unorientable unit clauses: 0
% 0.49/0.68  #    Negative unit clauses             : 7
% 0.49/0.68  #    Non-unit-clauses                  : 534
% 0.49/0.68  # Current number of unprocessed clauses: 7630
% 0.49/0.68  # ...number of literals in the above   : 30743
% 0.49/0.68  # Current number of archived formulas  : 0
% 0.49/0.68  # Current number of archived clauses   : 162
% 0.49/0.68  # Clause-clause subsumption calls (NU) : 67927
% 0.49/0.68  # Rec. Clause-clause subsumption calls : 46675
% 0.49/0.68  # Non-unit clause-clause subsumptions  : 1860
% 0.49/0.68  # Unit Clause-clause subsumption calls : 1251
% 0.49/0.68  # Rewrite failures with RHS unbound    : 0
% 0.49/0.68  # BW rewrite match attempts            : 144
% 0.49/0.68  # BW rewrite match successes           : 32
% 0.49/0.68  # Condensation attempts                : 0
% 0.49/0.68  # Condensation successes               : 0
% 0.49/0.68  # Termbank termtop insertions          : 234156
% 0.49/0.68  
% 0.49/0.68  # -------------------------------------------------
% 0.49/0.68  # User time                : 0.321 s
% 0.49/0.68  # System time              : 0.012 s
% 0.49/0.68  # Total time               : 0.333 s
% 0.49/0.68  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
