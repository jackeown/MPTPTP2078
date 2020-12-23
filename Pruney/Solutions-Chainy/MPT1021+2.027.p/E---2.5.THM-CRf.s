%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:10 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 969 expanded)
%              Number of clauses        :   92 ( 388 expanded)
%              Number of leaves         :   19 ( 237 expanded)
%              Depth                    :   22
%              Number of atoms          :  430 (3819 expanded)
%              Number of equality atoms :  129 ( 547 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
        & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(dt_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v1_funct_1(k2_funct_2(X1,X2))
        & v1_funct_2(k2_funct_2(X1,X2),X1,X1)
        & v3_funct_2(k2_funct_2(X1,X2),X1,X1)
        & m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

fof(c_0_20,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,plain,(
    ! [X30] : m1_subset_1(k6_relat_1(X30),k1_zfmisc_1(k2_zfmisc_1(X30,X30))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & v3_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_partfun1(esk1_0))
      | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_partfun1(esk1_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_23,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r2_relset_1(X26,X27,X28,X29)
        | X28 = X29
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X28 != X29
        | r2_relset_1(X26,X27,X28,X29)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ( k2_zfmisc_1(X8,X9) != k1_xboole_0
        | X8 = k1_xboole_0
        | X9 = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X8,X9) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k1_xboole_0)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1)) ),
    inference(pm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(pm,[status(thm)],[c_0_24,c_0_27])).

fof(c_0_34,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ~ v1_funct_1(X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | ~ v1_funct_1(X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k1_partfun1(X41,X42,X43,X44,X45,X46) = k5_relat_1(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_35,plain,(
    ! [X47,X48] :
      ( ~ v1_funct_1(X48)
      | ~ v1_funct_2(X48,X47,X47)
      | ~ v3_funct_2(X48,X47,X47)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X47)))
      | k2_funct_2(X47,X48) = k2_funct_1(X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_36,plain,(
    ! [X31,X32,X33] :
      ( ( v1_funct_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v3_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v2_funct_1(X33)
        | ~ v1_funct_1(X33)
        | ~ v3_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( v2_funct_2(X33,X32)
        | ~ v1_funct_1(X33)
        | ~ v3_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_37,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_38,negated_conjecture,
    ( esk2_0 = X1
    | ~ r2_relset_1(esk1_0,esk1_0,esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(pm,[status(thm)],[c_0_28,c_0_27])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r1_tarski(k6_relat_1(X1),k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk2_0,X1)
    | esk2_0 != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(pm,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0)
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_33,c_0_31])).

fof(c_0_43,plain,(
    ! [X49] : k6_partfun1(X49) = k6_relat_1(X49) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_44,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_46,plain,(
    ! [X16] :
      ( ( k5_relat_1(X16,k2_funct_1(X16)) = k6_relat_1(k1_relat_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( k5_relat_1(k2_funct_1(X16),X16) = k6_relat_1(k2_relat_1(X16))
        | ~ v2_funct_1(X16)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_47,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_49,negated_conjecture,
    ( v3_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_50,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_51,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_52,plain,(
    ! [X39,X40] :
      ( ( v1_funct_1(k2_funct_2(X39,X40))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X39,X39)
        | ~ v3_funct_2(X40,X39,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X39))) )
      & ( v1_funct_2(k2_funct_2(X39,X40),X39,X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X39,X39)
        | ~ v3_funct_2(X40,X39,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X39))) )
      & ( v3_funct_2(k2_funct_2(X39,X40),X39,X39)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X39,X39)
        | ~ v3_funct_2(X40,X39,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X39))) )
      & ( m1_subset_1(k2_funct_2(X39,X40),k1_zfmisc_1(k2_zfmisc_1(X39,X39)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X39,X39)
        | ~ v3_funct_2(X40,X39,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

fof(c_0_53,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_relset_1(X23,X24,X25) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = k6_relat_1(esk1_0)
    | ~ r2_relset_1(esk1_0,esk1_0,esk2_0,k6_relat_1(esk1_0)) ),
    inference(pm,[status(thm)],[c_0_38,c_0_25])).

cnf(c_0_55,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk2_0,esk2_0) ),
    inference(pm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_39,c_0_42])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_partfun1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_59,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( k1_partfun1(X1,X2,esk1_0,esk1_0,X3,esk2_0) = k5_relat_1(X3,esk2_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44,c_0_27]),c_0_45])])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,negated_conjecture,
    ( k2_funct_1(esk2_0) = k2_funct_2(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_27]),c_0_48]),c_0_49]),c_0_45])])).

cnf(c_0_64,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_27]),c_0_49]),c_0_45])])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(pm,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_66,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 = k6_relat_1(esk1_0)
    | k1_xboole_0 != esk1_0
    | ~ r2_relset_1(esk1_0,esk1_0,esk2_0,k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk2_0,k1_xboole_0)
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( k1_partfun1(X1,X2,esk1_0,esk1_0,X3,esk2_0) = k5_relat_1(X3,esk2_0)
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk1_0,esk2_0),esk2_0) = k6_relat_1(k2_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_45]),c_0_65])])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_27]),c_0_48]),c_0_49]),c_0_45])])).

cnf(c_0_74,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,X1,X2,esk2_0,X3) = k5_relat_1(esk2_0,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44,c_0_27]),c_0_45])])).

cnf(c_0_75,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_76,negated_conjecture,
    ( k1_relat_1(esk2_0) = k1_relset_1(esk1_0,esk1_0,esk2_0) ),
    inference(pm,[status(thm)],[c_0_67,c_0_27])).

cnf(c_0_77,negated_conjecture,
    ( esk2_0 = k6_relat_1(esk1_0)
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0))
    | ~ r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_71]),c_0_72]),c_0_73])])).

cnf(c_0_79,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,X1,X2,esk2_0,X3) = k5_relat_1(esk2_0,X3)
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(pm,[status(thm)],[c_0_74,c_0_61])).

cnf(c_0_80,negated_conjecture,
    ( k5_relat_1(esk2_0,k2_funct_2(esk1_0,esk2_0)) = k6_relat_1(k1_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75,c_0_63]),c_0_76]),c_0_64]),c_0_45]),c_0_65])])).

cnf(c_0_81,negated_conjecture,
    ( k2_funct_1(k6_relat_1(esk1_0)) = k2_funct_2(esk1_0,esk2_0)
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_63,c_0_77])).

cnf(c_0_82,plain,
    ( k2_funct_2(X1,k6_relat_1(X1)) = k2_funct_1(k6_relat_1(X1))
    | ~ v1_funct_2(k6_relat_1(X1),X1,X1)
    | ~ v3_funct_2(k6_relat_1(X1),X1,X1)
    | ~ v1_funct_1(k6_relat_1(X1)) ),
    inference(pm,[status(thm)],[c_0_47,c_0_25])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(k1_relset_1(esk1_0,esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0))
    | ~ r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_73])])).

fof(c_0_84,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X36 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != k1_xboole_0
        | v1_funct_2(X36,X34,X35)
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_85,negated_conjecture,
    ( k2_funct_2(esk1_0,esk2_0) = k2_funct_2(esk1_0,k6_relat_1(esk1_0))
    | k1_xboole_0 != esk1_0
    | ~ v1_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)
    | ~ v1_funct_1(k6_relat_1(esk1_0)) ),
    inference(pm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_1(k6_relat_1(esk1_0))
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_45,c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( k1_xboole_0 != esk1_0
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(k1_relset_1(esk1_0,esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)
    | ~ r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(pm,[status(thm)],[c_0_83,c_0_55])).

cnf(c_0_88,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_89,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_90,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( k2_funct_2(esk1_0,esk2_0) = k2_funct_2(esk1_0,k6_relat_1(esk1_0))
    | k1_xboole_0 != esk1_0
    | ~ v1_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)
    | ~ v3_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0) ),
    inference(pm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_48,c_0_77])).

cnf(c_0_93,negated_conjecture,
    ( k1_xboole_0 != esk1_0
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(k1_relset_1(esk1_0,esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_87,c_0_57]),c_0_88]),c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    | k1_xboole_0 != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_90,c_0_27]),c_0_48])])).

cnf(c_0_95,negated_conjecture,
    ( k2_funct_2(esk1_0,esk2_0) = k2_funct_2(esk1_0,k6_relat_1(esk1_0))
    | k1_xboole_0 != esk1_0
    | ~ v3_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0) ),
    inference(pm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( v3_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_49,c_0_77])).

cnf(c_0_97,negated_conjecture,
    ( k1_xboole_0 != esk1_0
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0)) ),
    inference(pm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_99,negated_conjecture,
    ( k2_funct_2(esk1_0,esk2_0) = k2_funct_2(esk1_0,k6_relat_1(esk1_0))
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_100,negated_conjecture,
    ( k1_xboole_0 != esk1_0
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_funct_2(esk1_0,esk2_0),k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_97,c_0_31])).

cnf(c_0_101,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),X2)
    | k6_relat_1(X1) != X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(pm,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | k1_xboole_0 != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_98,c_0_99]),c_0_48]),c_0_49]),c_0_45]),c_0_27])])).

cnf(c_0_103,negated_conjecture,
    ( k1_xboole_0 != esk1_0
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_100,c_0_77])).

cnf(c_0_104,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1)) ),
    inference(pm,[status(thm)],[c_0_101,c_0_25])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_102,c_0_31])).

cnf(c_0_106,negated_conjecture,
    ( k1_xboole_0 != esk1_0
    | ~ r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_xboole_0)
    | k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_24,c_0_105])).

cnf(c_0_108,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_104,c_0_55])).

cnf(c_0_109,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_110,negated_conjecture,
    ( k1_xboole_0 != esk1_0
    | ~ r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_111,plain,
    ( r2_relset_1(X1,X1,k1_xboole_0,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_108,c_0_55])).

cnf(c_0_112,plain,
    ( k1_partfun1(X1,X1,X2,X3,k2_funct_2(X1,X4),X5) = k5_relat_1(k2_funct_2(X1,X4),X5)
    | ~ v1_funct_2(X4,X1,X1)
    | ~ v3_funct_2(X4,X1,X1)
    | ~ v1_funct_1(k2_funct_2(X1,X4))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(pm,[status(thm)],[c_0_44,c_0_98])).

cnf(c_0_113,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    | k1_xboole_0 = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109,c_0_27]),c_0_48])])).

cnf(c_0_114,negated_conjecture,
    ( k1_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_110,c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_112]),c_0_72]),c_0_48]),c_0_49]),c_0_73]),c_0_45]),c_0_27])])).

cnf(c_0_116,plain,
    ( k1_partfun1(X1,X2,X3,X3,X4,k2_funct_2(X3,X5)) = k5_relat_1(X4,k2_funct_2(X3,X5))
    | ~ v1_funct_2(X5,X3,X3)
    | ~ v3_funct_2(X5,X3,X3)
    | ~ v1_funct_1(k2_funct_2(X3,X5))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(pm,[status(thm)],[c_0_44,c_0_98])).

cnf(c_0_117,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(sr,[status(thm)],[c_0_113,c_0_114])).

fof(c_0_118,plain,(
    ! [X37,X38] :
      ( ( ~ v2_funct_2(X38,X37)
        | k2_relat_1(X38) = X37
        | ~ v1_relat_1(X38)
        | ~ v5_relat_1(X38,X37) )
      & ( k2_relat_1(X38) != X37
        | v2_funct_2(X38,X37)
        | ~ v1_relat_1(X38)
        | ~ v5_relat_1(X38,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

fof(c_0_119,plain,(
    ! [X20,X21,X22] :
      ( ( v4_relat_1(X22,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v5_relat_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_120,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115,c_0_116]),c_0_80]),c_0_117]),c_0_104]),c_0_48]),c_0_49]),c_0_73]),c_0_45]),c_0_27])])).

cnf(c_0_121,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_122,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_123,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( ~ v2_funct_2(esk2_0,X1)
    | ~ r2_relset_1(esk1_0,esk1_0,k6_relat_1(X1),k6_relat_1(esk1_0))
    | ~ v5_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_120,c_0_121]),c_0_65])])).

cnf(c_0_125,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),X2)
    | k6_relat_1(X1) != X2
    | ~ r1_tarski(X2,k2_zfmisc_1(X1,X1)) ),
    inference(pm,[status(thm)],[c_0_101,c_0_61])).

cnf(c_0_126,negated_conjecture,
    ( v2_funct_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_122,c_0_27]),c_0_49]),c_0_45])])).

cnf(c_0_127,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(pm,[status(thm)],[c_0_123,c_0_27])).

cnf(c_0_128,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_124,c_0_125]),c_0_126]),c_0_127]),c_0_30])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.62/0.77  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.62/0.77  # and selection function NoSelection.
% 0.62/0.77  #
% 0.62/0.77  # Preprocessing time       : 0.029 s
% 0.62/0.77  
% 0.62/0.77  # Proof found!
% 0.62/0.77  # SZS status Theorem
% 0.62/0.77  # SZS output start CNFRefutation
% 0.62/0.77  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 0.62/0.77  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.62/0.77  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.62/0.77  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.62/0.77  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.62/0.77  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.62/0.77  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.62/0.77  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 0.62/0.77  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 0.62/0.77  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.62/0.77  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.62/0.77  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.62/0.77  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 0.62/0.77  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.62/0.77  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.62/0.77  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.62/0.77  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.62/0.77  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 0.62/0.77  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.62/0.77  fof(c_0_19, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 0.62/0.77  fof(c_0_20, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.62/0.77  fof(c_0_21, plain, ![X30]:m1_subset_1(k6_relat_1(X30),k1_zfmisc_1(k2_zfmisc_1(X30,X30))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.62/0.77  fof(c_0_22, negated_conjecture, ((((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&v3_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_partfun1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_partfun1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.62/0.77  fof(c_0_23, plain, ![X26, X27, X28, X29]:((~r2_relset_1(X26,X27,X28,X29)|X28=X29|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(X28!=X29|r2_relset_1(X26,X27,X28,X29)|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.62/0.77  cnf(c_0_24, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.62/0.77  cnf(c_0_25, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.62/0.77  fof(c_0_26, plain, ![X8, X9]:((k2_zfmisc_1(X8,X9)!=k1_xboole_0|(X8=k1_xboole_0|X9=k1_xboole_0))&((X8!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0)&(X9!=k1_xboole_0|k2_zfmisc_1(X8,X9)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.62/0.77  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.77  cnf(c_0_28, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.62/0.77  fof(c_0_29, plain, ![X7]:(~r1_tarski(X7,k1_xboole_0)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.62/0.77  cnf(c_0_30, plain, (r1_tarski(k6_relat_1(X1),k2_zfmisc_1(X1,X1))), inference(pm,[status(thm)],[c_0_24, c_0_25])).
% 0.62/0.77  cnf(c_0_31, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.62/0.77  cnf(c_0_32, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.62/0.77  cnf(c_0_33, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(esk1_0,esk1_0))), inference(pm,[status(thm)],[c_0_24, c_0_27])).
% 0.62/0.77  fof(c_0_34, plain, ![X41, X42, X43, X44, X45, X46]:(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k1_partfun1(X41,X42,X43,X44,X45,X46)=k5_relat_1(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.62/0.77  fof(c_0_35, plain, ![X47, X48]:(~v1_funct_1(X48)|~v1_funct_2(X48,X47,X47)|~v3_funct_2(X48,X47,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X47,X47)))|k2_funct_2(X47,X48)=k2_funct_1(X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 0.62/0.77  fof(c_0_36, plain, ![X31, X32, X33]:(((v1_funct_1(X33)|(~v1_funct_1(X33)|~v3_funct_2(X33,X31,X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))&(v2_funct_1(X33)|(~v1_funct_1(X33)|~v3_funct_2(X33,X31,X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(v2_funct_2(X33,X32)|(~v1_funct_1(X33)|~v3_funct_2(X33,X31,X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 0.62/0.77  fof(c_0_37, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.62/0.77  cnf(c_0_38, negated_conjecture, (esk2_0=X1|~r2_relset_1(esk1_0,esk1_0,esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(pm,[status(thm)],[c_0_28, c_0_27])).
% 0.62/0.77  cnf(c_0_39, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.77  cnf(c_0_40, plain, (r1_tarski(k6_relat_1(X1),k1_xboole_0)|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_30, c_0_31])).
% 0.62/0.77  cnf(c_0_41, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk2_0,X1)|esk2_0!=X1|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(pm,[status(thm)],[c_0_32, c_0_27])).
% 0.62/0.77  cnf(c_0_42, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_33, c_0_31])).
% 0.62/0.77  fof(c_0_43, plain, ![X49]:k6_partfun1(X49)=k6_relat_1(X49), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.62/0.77  cnf(c_0_44, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.62/0.77  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.77  fof(c_0_46, plain, ![X16]:((k5_relat_1(X16,k2_funct_1(X16))=k6_relat_1(k1_relat_1(X16))|~v2_funct_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(k5_relat_1(k2_funct_1(X16),X16)=k6_relat_1(k2_relat_1(X16))|~v2_funct_1(X16)|(~v1_relat_1(X16)|~v1_funct_1(X16)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.62/0.77  cnf(c_0_47, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.62/0.77  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.77  cnf(c_0_49, negated_conjecture, (v3_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.77  cnf(c_0_50, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.62/0.77  cnf(c_0_51, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.62/0.77  fof(c_0_52, plain, ![X39, X40]:((((v1_funct_1(k2_funct_2(X39,X40))|(~v1_funct_1(X40)|~v1_funct_2(X40,X39,X39)|~v3_funct_2(X40,X39,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X39)))))&(v1_funct_2(k2_funct_2(X39,X40),X39,X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,X39,X39)|~v3_funct_2(X40,X39,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X39))))))&(v3_funct_2(k2_funct_2(X39,X40),X39,X39)|(~v1_funct_1(X40)|~v1_funct_2(X40,X39,X39)|~v3_funct_2(X40,X39,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X39))))))&(m1_subset_1(k2_funct_2(X39,X40),k1_zfmisc_1(k2_zfmisc_1(X39,X39)))|(~v1_funct_1(X40)|~v1_funct_2(X40,X39,X39)|~v3_funct_2(X40,X39,X39)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X39,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 0.62/0.77  fof(c_0_53, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k1_relset_1(X23,X24,X25)=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.62/0.77  cnf(c_0_54, negated_conjecture, (esk2_0=k6_relat_1(esk1_0)|~r2_relset_1(esk1_0,esk1_0,esk2_0,k6_relat_1(esk1_0))), inference(pm,[status(thm)],[c_0_38, c_0_25])).
% 0.62/0.77  cnf(c_0_55, plain, (k6_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_39, c_0_40])).
% 0.62/0.77  cnf(c_0_56, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk2_0,esk2_0)), inference(pm,[status(thm)],[c_0_41, c_0_27])).
% 0.62/0.77  cnf(c_0_57, negated_conjecture, (esk2_0=k1_xboole_0|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_39, c_0_42])).
% 0.62/0.77  cnf(c_0_58, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_partfun1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.62/0.77  cnf(c_0_59, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.62/0.77  cnf(c_0_60, negated_conjecture, (k1_partfun1(X1,X2,esk1_0,esk1_0,X3,esk2_0)=k5_relat_1(X3,esk2_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44, c_0_27]), c_0_45])])).
% 0.62/0.77  cnf(c_0_61, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.62/0.77  cnf(c_0_62, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.62/0.77  cnf(c_0_63, negated_conjecture, (k2_funct_1(esk2_0)=k2_funct_2(esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_27]), c_0_48]), c_0_49]), c_0_45])])).
% 0.62/0.77  cnf(c_0_64, negated_conjecture, (v2_funct_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_27]), c_0_49]), c_0_45])])).
% 0.62/0.77  cnf(c_0_65, negated_conjecture, (v1_relat_1(esk2_0)), inference(pm,[status(thm)],[c_0_51, c_0_27])).
% 0.62/0.77  cnf(c_0_66, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.62/0.77  cnf(c_0_67, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.62/0.77  cnf(c_0_68, negated_conjecture, (esk2_0=k6_relat_1(esk1_0)|k1_xboole_0!=esk1_0|~r2_relset_1(esk1_0,esk1_0,esk2_0,k1_xboole_0)), inference(pm,[status(thm)],[c_0_54, c_0_55])).
% 0.62/0.77  cnf(c_0_69, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk2_0,k1_xboole_0)|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_56, c_0_57])).
% 0.62/0.77  cnf(c_0_70, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,k2_funct_2(esk1_0,esk2_0),esk2_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59])).
% 0.62/0.77  cnf(c_0_71, negated_conjecture, (k1_partfun1(X1,X2,esk1_0,esk1_0,X3,esk2_0)=k5_relat_1(X3,esk2_0)|~v1_funct_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 0.62/0.77  cnf(c_0_72, negated_conjecture, (k5_relat_1(k2_funct_2(esk1_0,esk2_0),esk2_0)=k6_relat_1(k2_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_45]), c_0_65])])).
% 0.62/0.77  cnf(c_0_73, negated_conjecture, (v1_funct_1(k2_funct_2(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_27]), c_0_48]), c_0_49]), c_0_45])])).
% 0.62/0.77  cnf(c_0_74, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,X1,X2,esk2_0,X3)=k5_relat_1(esk2_0,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_44, c_0_27]), c_0_45])])).
% 0.62/0.77  cnf(c_0_75, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.62/0.77  cnf(c_0_76, negated_conjecture, (k1_relat_1(esk2_0)=k1_relset_1(esk1_0,esk1_0,esk2_0)), inference(pm,[status(thm)],[c_0_67, c_0_27])).
% 0.62/0.77  cnf(c_0_77, negated_conjecture, (esk2_0=k6_relat_1(esk1_0)|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_68, c_0_69])).
% 0.62/0.77  cnf(c_0_78, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0))|~r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_71]), c_0_72]), c_0_73])])).
% 0.62/0.77  cnf(c_0_79, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,X1,X2,esk2_0,X3)=k5_relat_1(esk2_0,X3)|~v1_funct_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(pm,[status(thm)],[c_0_74, c_0_61])).
% 0.62/0.77  cnf(c_0_80, negated_conjecture, (k5_relat_1(esk2_0,k2_funct_2(esk1_0,esk2_0))=k6_relat_1(k1_relset_1(esk1_0,esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75, c_0_63]), c_0_76]), c_0_64]), c_0_45]), c_0_65])])).
% 0.62/0.77  cnf(c_0_81, negated_conjecture, (k2_funct_1(k6_relat_1(esk1_0))=k2_funct_2(esk1_0,esk2_0)|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_63, c_0_77])).
% 0.62/0.77  cnf(c_0_82, plain, (k2_funct_2(X1,k6_relat_1(X1))=k2_funct_1(k6_relat_1(X1))|~v1_funct_2(k6_relat_1(X1),X1,X1)|~v3_funct_2(k6_relat_1(X1),X1,X1)|~v1_funct_1(k6_relat_1(X1))), inference(pm,[status(thm)],[c_0_47, c_0_25])).
% 0.62/0.77  cnf(c_0_83, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k6_relat_1(k1_relset_1(esk1_0,esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0))|~r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78, c_0_79]), c_0_80]), c_0_73])])).
% 0.62/0.77  fof(c_0_84, plain, ![X34, X35, X36]:((((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))))&((~v1_funct_2(X36,X34,X35)|X36=k1_xboole_0|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X36!=k1_xboole_0|v1_funct_2(X36,X34,X35)|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.62/0.77  cnf(c_0_85, negated_conjecture, (k2_funct_2(esk1_0,esk2_0)=k2_funct_2(esk1_0,k6_relat_1(esk1_0))|k1_xboole_0!=esk1_0|~v1_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)|~v3_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)|~v1_funct_1(k6_relat_1(esk1_0))), inference(pm,[status(thm)],[c_0_81, c_0_82])).
% 0.62/0.77  cnf(c_0_86, negated_conjecture, (v1_funct_1(k6_relat_1(esk1_0))|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_45, c_0_77])).
% 0.62/0.77  cnf(c_0_87, negated_conjecture, (k1_xboole_0!=esk1_0|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(k1_relset_1(esk1_0,esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k1_xboole_0)|~r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0))), inference(pm,[status(thm)],[c_0_83, c_0_55])).
% 0.62/0.77  cnf(c_0_88, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.62/0.77  cnf(c_0_89, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.62/0.77  cnf(c_0_90, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.62/0.77  cnf(c_0_91, negated_conjecture, (k2_funct_2(esk1_0,esk2_0)=k2_funct_2(esk1_0,k6_relat_1(esk1_0))|k1_xboole_0!=esk1_0|~v1_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)|~v3_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)), inference(pm,[status(thm)],[c_0_85, c_0_86])).
% 0.62/0.77  cnf(c_0_92, negated_conjecture, (v1_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_48, c_0_77])).
% 0.62/0.77  cnf(c_0_93, negated_conjecture, (k1_xboole_0!=esk1_0|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(k1_relset_1(esk1_0,esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_87, c_0_57]), c_0_88]), c_0_89])).
% 0.62/0.77  cnf(c_0_94, negated_conjecture, (k1_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0|k1_xboole_0!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_90, c_0_27]), c_0_48])])).
% 0.62/0.77  cnf(c_0_95, negated_conjecture, (k2_funct_2(esk1_0,esk2_0)=k2_funct_2(esk1_0,k6_relat_1(esk1_0))|k1_xboole_0!=esk1_0|~v3_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)), inference(pm,[status(thm)],[c_0_91, c_0_92])).
% 0.62/0.77  cnf(c_0_96, negated_conjecture, (v3_funct_2(k6_relat_1(esk1_0),esk1_0,esk1_0)|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_49, c_0_77])).
% 0.62/0.77  cnf(c_0_97, negated_conjecture, (k1_xboole_0!=esk1_0|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_funct_2(esk1_0,esk2_0),k2_zfmisc_1(esk1_0,esk1_0))), inference(pm,[status(thm)],[c_0_93, c_0_94])).
% 0.62/0.77  cnf(c_0_98, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.62/0.77  cnf(c_0_99, negated_conjecture, (k2_funct_2(esk1_0,esk2_0)=k2_funct_2(esk1_0,k6_relat_1(esk1_0))|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_95, c_0_96])).
% 0.62/0.77  cnf(c_0_100, negated_conjecture, (k1_xboole_0!=esk1_0|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_funct_2(esk1_0,esk2_0),k1_xboole_0)), inference(pm,[status(thm)],[c_0_97, c_0_31])).
% 0.62/0.77  cnf(c_0_101, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),X2)|k6_relat_1(X1)!=X2|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(pm,[status(thm)],[c_0_32, c_0_25])).
% 0.62/0.77  cnf(c_0_102, negated_conjecture, (m1_subset_1(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))|k1_xboole_0!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_98, c_0_99]), c_0_48]), c_0_49]), c_0_45]), c_0_27])])).
% 0.62/0.77  cnf(c_0_103, negated_conjecture, (k1_xboole_0!=esk1_0|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(esk1_0),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_xboole_0)), inference(pm,[status(thm)],[c_0_100, c_0_77])).
% 0.62/0.77  cnf(c_0_104, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1))), inference(pm,[status(thm)],[c_0_101, c_0_25])).
% 0.62/0.77  cnf(c_0_105, negated_conjecture, (m1_subset_1(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_zfmisc_1(k1_xboole_0))|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_102, c_0_31])).
% 0.62/0.77  cnf(c_0_106, negated_conjecture, (k1_xboole_0!=esk1_0|~r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 0.62/0.77  cnf(c_0_107, negated_conjecture, (r1_tarski(k2_funct_2(esk1_0,k6_relat_1(esk1_0)),k1_xboole_0)|k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_24, c_0_105])).
% 0.62/0.77  cnf(c_0_108, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),k1_xboole_0)|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_104, c_0_55])).
% 0.62/0.77  cnf(c_0_109, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.62/0.77  cnf(c_0_110, negated_conjecture, (k1_xboole_0!=esk1_0|~r2_relset_1(esk1_0,esk1_0,k1_xboole_0,k1_xboole_0)), inference(pm,[status(thm)],[c_0_106, c_0_107])).
% 0.62/0.77  cnf(c_0_111, plain, (r2_relset_1(X1,X1,k1_xboole_0,k1_xboole_0)|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_108, c_0_55])).
% 0.62/0.77  cnf(c_0_112, plain, (k1_partfun1(X1,X1,X2,X3,k2_funct_2(X1,X4),X5)=k5_relat_1(k2_funct_2(X1,X4),X5)|~v1_funct_2(X4,X1,X1)|~v3_funct_2(X4,X1,X1)|~v1_funct_1(k2_funct_2(X1,X4))|~v1_funct_1(X5)|~v1_funct_1(X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(pm,[status(thm)],[c_0_44, c_0_98])).
% 0.62/0.77  cnf(c_0_113, negated_conjecture, (k1_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0|k1_xboole_0=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109, c_0_27]), c_0_48])])).
% 0.62/0.77  cnf(c_0_114, negated_conjecture, (k1_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_110, c_0_111])).
% 0.62/0.77  cnf(c_0_115, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk2_0,k2_funct_2(esk1_0,esk2_0)),k6_relat_1(esk1_0))|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_112]), c_0_72]), c_0_48]), c_0_49]), c_0_73]), c_0_45]), c_0_27])])).
% 0.62/0.77  cnf(c_0_116, plain, (k1_partfun1(X1,X2,X3,X3,X4,k2_funct_2(X3,X5))=k5_relat_1(X4,k2_funct_2(X3,X5))|~v1_funct_2(X5,X3,X3)|~v3_funct_2(X5,X3,X3)|~v1_funct_1(k2_funct_2(X3,X5))|~v1_funct_1(X4)|~v1_funct_1(X5)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(pm,[status(thm)],[c_0_44, c_0_98])).
% 0.62/0.77  cnf(c_0_117, negated_conjecture, (k1_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0), inference(sr,[status(thm)],[c_0_113, c_0_114])).
% 0.62/0.77  fof(c_0_118, plain, ![X37, X38]:((~v2_funct_2(X38,X37)|k2_relat_1(X38)=X37|(~v1_relat_1(X38)|~v5_relat_1(X38,X37)))&(k2_relat_1(X38)!=X37|v2_funct_2(X38,X37)|(~v1_relat_1(X38)|~v5_relat_1(X38,X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.62/0.77  fof(c_0_119, plain, ![X20, X21, X22]:((v4_relat_1(X22,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(v5_relat_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.62/0.77  cnf(c_0_120, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,k6_relat_1(k2_relat_1(esk2_0)),k6_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115, c_0_116]), c_0_80]), c_0_117]), c_0_104]), c_0_48]), c_0_49]), c_0_73]), c_0_45]), c_0_27])])).
% 0.62/0.77  cnf(c_0_121, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.62/0.77  cnf(c_0_122, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.62/0.77  cnf(c_0_123, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_119])).
% 0.62/0.77  cnf(c_0_124, negated_conjecture, (~v2_funct_2(esk2_0,X1)|~r2_relset_1(esk1_0,esk1_0,k6_relat_1(X1),k6_relat_1(esk1_0))|~v5_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_120, c_0_121]), c_0_65])])).
% 0.62/0.77  cnf(c_0_125, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),X2)|k6_relat_1(X1)!=X2|~r1_tarski(X2,k2_zfmisc_1(X1,X1))), inference(pm,[status(thm)],[c_0_101, c_0_61])).
% 0.62/0.77  cnf(c_0_126, negated_conjecture, (v2_funct_2(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_122, c_0_27]), c_0_49]), c_0_45])])).
% 0.62/0.77  cnf(c_0_127, negated_conjecture, (v5_relat_1(esk2_0,esk1_0)), inference(pm,[status(thm)],[c_0_123, c_0_27])).
% 0.62/0.77  cnf(c_0_128, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_124, c_0_125]), c_0_126]), c_0_127]), c_0_30])]), ['proof']).
% 0.62/0.77  # SZS output end CNFRefutation
% 0.62/0.77  # Proof object total steps             : 129
% 0.62/0.77  # Proof object clause steps            : 92
% 0.62/0.77  # Proof object formula steps           : 37
% 0.62/0.77  # Proof object conjectures             : 60
% 0.62/0.77  # Proof object clause conjectures      : 57
% 0.62/0.77  # Proof object formula conjectures     : 3
% 0.62/0.77  # Proof object initial clauses used    : 29
% 0.62/0.77  # Proof object initial formulas used   : 19
% 0.62/0.77  # Proof object generating inferences   : 60
% 0.62/0.77  # Proof object simplifying inferences  : 71
% 0.62/0.77  # Training examples: 0 positive, 0 negative
% 0.62/0.77  # Parsed axioms                        : 22
% 0.62/0.77  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.77  # Initial clauses                      : 46
% 0.62/0.77  # Removed in clause preprocessing      : 3
% 0.62/0.77  # Initial clauses in saturation        : 43
% 0.62/0.77  # Processed clauses                    : 3855
% 0.62/0.77  # ...of these trivial                  : 68
% 0.62/0.77  # ...subsumed                          : 2663
% 0.62/0.77  # ...remaining for further processing  : 1124
% 0.62/0.77  # Other redundant clauses eliminated   : 0
% 0.62/0.77  # Clauses deleted for lack of memory   : 0
% 0.62/0.77  # Backward-subsumed                    : 139
% 0.62/0.77  # Backward-rewritten                   : 71
% 0.62/0.77  # Generated clauses                    : 30868
% 0.62/0.77  # ...of the previous two non-trivial   : 28335
% 0.62/0.77  # Contextual simplify-reflections      : 0
% 0.62/0.77  # Paramodulations                      : 30832
% 0.62/0.77  # Factorizations                       : 0
% 0.62/0.77  # Equation resolutions                 : 29
% 0.62/0.77  # Propositional unsat checks           : 0
% 0.62/0.77  #    Propositional check models        : 0
% 0.62/0.77  #    Propositional check unsatisfiable : 0
% 0.62/0.77  #    Propositional clauses             : 0
% 0.62/0.77  #    Propositional clauses after purity: 0
% 0.62/0.77  #    Propositional unsat core size     : 0
% 0.62/0.77  #    Propositional preprocessing time  : 0.000
% 0.62/0.77  #    Propositional encoding time       : 0.000
% 0.62/0.77  #    Propositional solver time         : 0.000
% 0.62/0.77  #    Success case prop preproc time    : 0.000
% 0.62/0.77  #    Success case prop encoding time   : 0.000
% 0.62/0.77  #    Success case prop solver time     : 0.000
% 0.62/0.77  # Current number of processed clauses  : 907
% 0.62/0.77  #    Positive orientable unit clauses  : 80
% 0.62/0.77  #    Positive unorientable unit clauses: 1
% 0.62/0.77  #    Negative unit clauses             : 11
% 0.62/0.77  #    Non-unit-clauses                  : 815
% 0.62/0.77  # Current number of unprocessed clauses: 24200
% 0.62/0.77  # ...number of literals in the above   : 138022
% 0.62/0.77  # Current number of archived formulas  : 0
% 0.62/0.77  # Current number of archived clauses   : 218
% 0.62/0.77  # Clause-clause subsumption calls (NU) : 39213
% 0.62/0.77  # Rec. Clause-clause subsumption calls : 27650
% 0.62/0.77  # Non-unit clause-clause subsumptions  : 1658
% 0.62/0.77  # Unit Clause-clause subsumption calls : 2886
% 0.62/0.77  # Rewrite failures with RHS unbound    : 0
% 0.62/0.77  # BW rewrite match attempts            : 310
% 0.62/0.77  # BW rewrite match successes           : 25
% 0.62/0.77  # Condensation attempts                : 0
% 0.62/0.77  # Condensation successes               : 0
% 0.62/0.77  # Termbank termtop insertions          : 282963
% 0.62/0.77  
% 0.62/0.77  # -------------------------------------------------
% 0.62/0.77  # User time                : 0.414 s
% 0.62/0.77  # System time              : 0.018 s
% 0.62/0.77  # Total time               : 0.432 s
% 0.62/0.77  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
