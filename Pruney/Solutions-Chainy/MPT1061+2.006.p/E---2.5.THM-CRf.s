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
% DateTime   : Thu Dec  3 11:07:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  124 (2727 expanded)
%              Number of clauses        :   82 (1098 expanded)
%              Number of leaves         :   21 ( 670 expanded)
%              Depth                    :   18
%              Number of atoms          :  323 (12716 expanded)
%              Number of equality atoms :   96 (1475 expanded)
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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

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

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk1_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0)))
    & r1_tarski(esk2_0,esk1_0)
    & r1_tarski(k7_relset_1(esk1_0,esk4_0,esk5_0,esk2_0),esk3_0)
    & ( ~ v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0))
      | ~ v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)
      | ~ m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_24,plain,(
    ! [X42,X43,X44] :
      ( ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X43 = k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X42 = k1_relset_1(X42,X43,X44)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X42 != k1_relset_1(X42,X43,X44)
        | v1_funct_2(X44,X42,X43)
        | X42 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( ~ v1_funct_2(X44,X42,X43)
        | X44 = k1_xboole_0
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X44 != k1_xboole_0
        | v1_funct_2(X44,X42,X43)
        | X42 = k1_xboole_0
        | X43 != k1_xboole_0
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_28,plain,(
    ! [X49,X50,X51,X52] :
      ( ~ v1_funct_1(X51)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | k2_partfun1(X49,X50,X51,X52) = k7_relat_1(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_29,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | ~ r1_tarski(X24,k1_relat_1(X25))
      | k1_relat_1(k7_relat_1(X25,X24)) = X24 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_30,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(esk1_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk5_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X45,X46,X47,X48] :
      ( ( v1_funct_1(k2_partfun1(X45,X46,X47,X48))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( m1_subset_1(k2_partfun1(X45,X46,X47,X48),k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
        | ~ v1_funct_1(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_35,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk1_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_31]),c_0_32])])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

fof(c_0_40,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_relat_1(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_41,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k2_partfun1(esk1_0,esk4_0,esk5_0,X1) = k7_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_36])])).

fof(c_0_43,plain,(
    ! [X18,X19] : v1_relat_1(k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_44,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_45,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_relat_1(X41)
      | ~ r1_tarski(k1_relat_1(X41),X39)
      | ~ r1_tarski(k2_relat_1(X41),X40)
      | m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,X1)) = X1
    | esk4_0 = k1_xboole_0
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_26]),c_0_42]),c_0_36])])).

cnf(c_0_50,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_52,plain,(
    ! [X16,X17] :
      ( ( ~ v4_relat_1(X17,X16)
        | r1_tarski(k1_relat_1(X17),X16)
        | ~ v1_relat_1(X17) )
      & ( ~ r1_tarski(k1_relat_1(X17),X16)
        | v4_relat_1(X17,X16)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_53,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk5_0,esk2_0)) = esk2_0
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_58,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k7_relset_1(X35,X36,X37,X38) = k9_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk5_0,X1),esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk5_0,esk2_0)),X2)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_57])).

fof(c_0_63,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | k2_relat_1(k7_relat_1(X21,X20)) = k9_relat_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_64,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk5_0,X1)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_56])])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk5_0,esk2_0)),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k7_relset_1(esk1_0,esk4_0,esk5_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( k7_relset_1(esk1_0,esk4_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_26])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(esk5_0,X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_65]),c_0_56])])).

cnf(c_0_71,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ r1_tarski(k9_relat_1(esk5_0,esk2_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_39])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,esk2_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_74,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_75,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))
    | ~ r1_tarski(k9_relat_1(esk5_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_67]),c_0_39])])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_26]),c_0_36])])).

cnf(c_0_79,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_73])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78])])).

cnf(c_0_85,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_86,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,k7_relat_1(esk5_0,esk2_0)) = k1_relat_1(k7_relat_1(esk5_0,esk2_0))
    | esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_79])).

fof(c_0_87,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_88,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_62])).

fof(c_0_90,plain,(
    ! [X9] :
      ( ~ r1_tarski(X9,k1_xboole_0)
      | X9 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_91,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_92,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk5_0,esk2_0),k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk2_0),esk2_0,esk3_0)
    | ~ m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_42]),c_0_42])).

cnf(c_0_95,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v1_funct_2(k7_relat_1(esk5_0,esk2_0),esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_79]),c_0_55])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_97,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_88])).

cnf(c_0_98,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_88])).

cnf(c_0_99,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_62])).

cnf(c_0_100,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_101,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_102,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_103,negated_conjecture,
    ( k7_relat_1(esk5_0,esk2_0) = k2_zfmisc_1(esk1_0,esk3_0)
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),k7_relat_1(esk5_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_104,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_79])).

cnf(c_0_105,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_106,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_97]),c_0_98])])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_99])).

cnf(c_0_108,plain,
    ( k1_relat_1(k7_relat_1(X1,k1_xboole_0)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_110,negated_conjecture,
    ( k7_relat_1(esk5_0,esk2_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105]),c_0_105]),c_0_81])])).

cnf(c_0_111,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_106])).

cnf(c_0_112,plain,
    ( r1_tarski(k7_relat_1(X1,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1(X1,k1_xboole_0))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_113,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_115,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_110]),c_0_111])).

cnf(c_0_116,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk5_0,k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_56]),c_0_39])])).

cnf(c_0_118,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_113]),c_0_109])).

cnf(c_0_119,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_88]),c_0_111])).

cnf(c_0_120,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116])])).

cnf(c_0_121,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_117]),c_0_81])])).

cnf(c_0_122,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_88])])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_120]),c_0_121]),c_0_120]),c_0_122]),c_0_120]),c_0_121]),c_0_120]),c_0_109]),c_0_88])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___215_C46_F1_AE_CS_SP_PS_S2S
% 0.19/0.42  # and selection function SelectNewComplexAHP.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.037 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t178_funct_2, conjecture, ![X1, X2, X3, X4]:(~(v1_xboole_0(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=>((r1_tarski(X2,X1)&r1_tarski(k7_relset_1(X1,X4,X5,X2),X3))=>((v1_funct_1(k2_partfun1(X1,X4,X5,X2))&v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3))&m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 0.19/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.42  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.42  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.19/0.42  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.19/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.42  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.42  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.42  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.42  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.42  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.19/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.42  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4]:(~(v1_xboole_0(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=>((r1_tarski(X2,X1)&r1_tarski(k7_relset_1(X1,X4,X5,X2),X3))=>((v1_funct_1(k2_partfun1(X1,X4,X5,X2))&v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3))&m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))))))), inference(assume_negation,[status(cth)],[t178_funct_2])).
% 0.19/0.42  fof(c_0_22, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.42  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk1_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0))))&((r1_tarski(esk2_0,esk1_0)&r1_tarski(k7_relset_1(esk1_0,esk4_0,esk5_0,esk2_0),esk3_0))&(~v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0))|~v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)|~m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.19/0.42  fof(c_0_24, plain, ![X42, X43, X44]:((((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X43=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))&((~v1_funct_2(X44,X42,X43)|X42=k1_relset_1(X42,X43,X44)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X42!=k1_relset_1(X42,X43,X44)|v1_funct_2(X44,X42,X43)|X42!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))))&((~v1_funct_2(X44,X42,X43)|X44=k1_xboole_0|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(X44!=k1_xboole_0|v1_funct_2(X44,X42,X43)|X42=k1_xboole_0|X43!=k1_xboole_0|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.42  cnf(c_0_25, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  fof(c_0_27, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.42  fof(c_0_28, plain, ![X49, X50, X51, X52]:(~v1_funct_1(X51)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|k2_partfun1(X49,X50,X51,X52)=k7_relat_1(X51,X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.42  fof(c_0_29, plain, ![X24, X25]:(~v1_relat_1(X25)|(~r1_tarski(X24,k1_relat_1(X25))|k1_relat_1(k7_relat_1(X25,X24))=X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.19/0.42  cnf(c_0_30, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (k1_relset_1(esk1_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.42  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk5_0,esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_33, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  fof(c_0_34, plain, ![X45, X46, X47, X48]:((v1_funct_1(k2_partfun1(X45,X46,X47,X48))|(~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&(m1_subset_1(k2_partfun1(X45,X46,X47,X48),k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|(~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.19/0.42  cnf(c_0_35, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_37, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk5_0)=esk1_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_26]), c_0_31]), c_0_32])])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_26])).
% 0.19/0.42  fof(c_0_40, plain, ![X14, X15]:(~v1_relat_1(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_relat_1(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.42  cnf(c_0_41, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, (k2_partfun1(esk1_0,esk4_0,esk5_0,X1)=k7_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_26]), c_0_36])])).
% 0.19/0.42  fof(c_0_43, plain, ![X18, X19]:v1_relat_1(k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.42  fof(c_0_44, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.42  fof(c_0_45, plain, ![X39, X40, X41]:(~v1_relat_1(X41)|(~r1_tarski(k1_relat_1(X41),X39)|~r1_tarski(k2_relat_1(X41),X40)|m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,X1))=X1|esk4_0=k1_xboole_0|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (r1_tarski(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_48, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_26]), c_0_42]), c_0_36])])).
% 0.19/0.42  cnf(c_0_50, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.42  fof(c_0_51, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  fof(c_0_52, plain, ![X16, X17]:((~v4_relat_1(X17,X16)|r1_tarski(k1_relat_1(X17),X16)|~v1_relat_1(X17))&(~r1_tarski(k1_relat_1(X17),X16)|v4_relat_1(X17,X16)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.42  cnf(c_0_53, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.42  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (k1_relat_1(k7_relat_1(esk5_0,esk2_0))=esk2_0|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, (v1_relat_1(k7_relat_1(esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.19/0.42  cnf(c_0_57, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  fof(c_0_58, plain, ![X35, X36, X37, X38]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k7_relset_1(X35,X36,X37,X38)=k9_relat_1(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.42  cnf(c_0_59, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (v4_relat_1(k7_relat_1(esk5_0,X1),esk1_0)), inference(spm,[status(thm)],[c_0_53, c_0_49])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k2_relat_1(k7_relat_1(esk5_0,esk2_0)),X2)|~r1_tarski(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.19/0.42  cnf(c_0_62, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_57])).
% 0.19/0.42  fof(c_0_63, plain, ![X20, X21]:(~v1_relat_1(X21)|k2_relat_1(k7_relat_1(X21,X20))=k9_relat_1(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.42  cnf(c_0_64, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk5_0,X1)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_56])])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~r1_tarski(k2_relat_1(k7_relat_1(esk5_0,esk2_0)),X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.42  cnf(c_0_67, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (r1_tarski(k7_relset_1(esk1_0,esk4_0,esk5_0,esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (k7_relset_1(esk1_0,esk4_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_64, c_0_26])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))|~r1_tarski(k2_relat_1(k7_relat_1(esk5_0,X1)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_65]), c_0_56])])).
% 0.19/0.42  cnf(c_0_71, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~r1_tarski(k9_relat_1(esk5_0,esk2_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_39])])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,esk2_0),esk3_0)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.42  fof(c_0_74, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  fof(c_0_75, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,X2)))|~r1_tarski(k9_relat_1(esk5_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_67]), c_0_39])])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (~v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0))|~v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)|~m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (v1_funct_1(k2_partfun1(esk1_0,esk4_0,esk5_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_26]), c_0_36])])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.42  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.42  cnf(c_0_81, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.42  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.19/0.42  cnf(c_0_83, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_76, c_0_73])).
% 0.19/0.42  cnf(c_0_84, negated_conjecture, (~v1_funct_2(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),esk2_0,esk3_0)|~m1_subset_1(k2_partfun1(esk1_0,esk4_0,esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78])])).
% 0.19/0.42  cnf(c_0_85, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,k7_relat_1(esk5_0,esk2_0))=k1_relat_1(k7_relat_1(esk5_0,esk2_0))|esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_79])).
% 0.19/0.42  fof(c_0_87, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_88, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.19/0.42  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_54, c_0_62])).
% 0.19/0.42  fof(c_0_90, plain, ![X9]:(~r1_tarski(X9,k1_xboole_0)|X9=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.42  fof(c_0_91, plain, ![X22, X23]:(~v1_relat_1(X23)|r1_tarski(k1_relat_1(k7_relat_1(X23,X22)),X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.19/0.42  cnf(c_0_92, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_93, negated_conjecture, (r1_tarski(k7_relat_1(esk5_0,esk2_0),k2_zfmisc_1(esk1_0,esk3_0))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk2_0),esk2_0,esk3_0)|~m1_subset_1(k7_relat_1(esk5_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_42]), c_0_42])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0=k1_xboole_0|v1_funct_2(k7_relat_1(esk5_0,esk2_0),esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_79]), c_0_55])).
% 0.19/0.42  cnf(c_0_96, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.42  cnf(c_0_97, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_53, c_0_88])).
% 0.19/0.42  cnf(c_0_98, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_88])).
% 0.19/0.42  cnf(c_0_99, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_89, c_0_62])).
% 0.19/0.42  cnf(c_0_100, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.19/0.42  cnf(c_0_101, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.42  cnf(c_0_102, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.42  cnf(c_0_103, negated_conjecture, (k7_relat_1(esk5_0,esk2_0)=k2_zfmisc_1(esk1_0,esk3_0)|~r1_tarski(k2_zfmisc_1(esk1_0,esk3_0),k7_relat_1(esk5_0,esk2_0))), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.42  cnf(c_0_104, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_79])).
% 0.19/0.42  cnf(c_0_105, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_96])).
% 0.19/0.42  cnf(c_0_106, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_97]), c_0_98])])).
% 0.19/0.42  cnf(c_0_107, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_82, c_0_99])).
% 0.19/0.42  cnf(c_0_108, plain, (k1_relat_1(k7_relat_1(X1,k1_xboole_0))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.42  cnf(c_0_109, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_102])).
% 0.19/0.42  cnf(c_0_110, negated_conjecture, (k7_relat_1(esk5_0,esk2_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105]), c_0_105]), c_0_81])])).
% 0.19/0.42  cnf(c_0_111, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_106])).
% 0.19/0.42  cnf(c_0_112, plain, (r1_tarski(k7_relat_1(X1,k1_xboole_0),k1_xboole_0)|~v1_relat_1(k7_relat_1(X1,k1_xboole_0))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_108]), c_0_109])).
% 0.19/0.42  cnf(c_0_113, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_114, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_115, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_110]), c_0_111])).
% 0.19/0.42  cnf(c_0_116, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.42  cnf(c_0_117, negated_conjecture, (r1_tarski(k7_relat_1(esk5_0,k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_56]), c_0_39])])).
% 0.19/0.42  cnf(c_0_118, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_113]), c_0_109])).
% 0.19/0.42  cnf(c_0_119, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_88]), c_0_111])).
% 0.19/0.42  cnf(c_0_120, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116])])).
% 0.19/0.42  cnf(c_0_121, negated_conjecture, (k7_relat_1(esk5_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_117]), c_0_81])])).
% 0.19/0.42  cnf(c_0_122, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_88])])).
% 0.19/0.42  cnf(c_0_123, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_120]), c_0_121]), c_0_120]), c_0_122]), c_0_120]), c_0_121]), c_0_120]), c_0_109]), c_0_88])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 124
% 0.19/0.42  # Proof object clause steps            : 82
% 0.19/0.42  # Proof object formula steps           : 42
% 0.19/0.42  # Proof object conjectures             : 43
% 0.19/0.42  # Proof object clause conjectures      : 40
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 33
% 0.19/0.42  # Proof object initial formulas used   : 21
% 0.19/0.42  # Proof object generating inferences   : 44
% 0.19/0.42  # Proof object simplifying inferences  : 61
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 21
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 40
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 40
% 0.19/0.42  # Processed clauses                    : 493
% 0.19/0.42  # ...of these trivial                  : 31
% 0.19/0.42  # ...subsumed                          : 75
% 0.19/0.42  # ...remaining for further processing  : 387
% 0.19/0.42  # Other redundant clauses eliminated   : 2
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 6
% 0.19/0.42  # Backward-rewritten                   : 106
% 0.19/0.42  # Generated clauses                    : 1196
% 0.19/0.42  # ...of the previous two non-trivial   : 840
% 0.19/0.42  # Contextual simplify-reflections      : 4
% 0.19/0.42  # Paramodulations                      : 1186
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 10
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 234
% 0.19/0.42  #    Positive orientable unit clauses  : 100
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 1
% 0.19/0.42  #    Non-unit-clauses                  : 133
% 0.19/0.42  # Current number of unprocessed clauses: 384
% 0.19/0.42  # ...number of literals in the above   : 844
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 151
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 1593
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 1212
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 85
% 0.19/0.42  # Unit Clause-clause subsumption calls : 208
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 166
% 0.19/0.42  # BW rewrite match successes           : 21
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 20314
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.072 s
% 0.19/0.42  # System time              : 0.007 s
% 0.19/0.42  # Total time               : 0.079 s
% 0.19/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
