%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:00 EST 2020

% Result     : Theorem 0.76s
% Output     : CNFRefutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  110 (1095 expanded)
%              Number of clauses        :   73 ( 419 expanded)
%              Number of leaves         :   18 ( 261 expanded)
%              Depth                    :   14
%              Number of atoms          :  314 (6860 expanded)
%              Number of equality atoms :   78 (2182 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( ( k2_relset_1(X1,X2,X3) = X2
              & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
              & v2_funct_1(X3) )
           => ( X1 = k1_xboole_0
              | X2 = k1_xboole_0
              | X4 = k2_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X1)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
           => ( ( k2_relset_1(X1,X2,X3) = X2
                & r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
                & v2_funct_1(X3) )
             => ( X1 = k1_xboole_0
                | X2 = k1_xboole_0
                | X4 = k2_funct_1(X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_funct_2])).

fof(c_0_19,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))
    & v2_funct_1(esk3_0)
    & esk1_0 != k1_xboole_0
    & esk2_0 != k1_xboole_0
    & esk4_0 != k2_funct_1(esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_21,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_25,plain,(
    ! [X49] : k6_partfun1(X49) = k6_relat_1(X49) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_26,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | ~ v1_funct_1(X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k1_partfun1(X43,X44,X45,X46,X47,X48) = k5_relat_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( esk2_0 = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

fof(c_0_29,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | r1_tarski(k1_relat_1(k5_relat_1(X11,X12)),k1_relat_1(X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk3_0),esk1_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_36,plain,(
    ! [X9,X10] :
      ( ( ~ v4_relat_1(X10,X9)
        | r1_tarski(k1_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k1_relat_1(X10),X9)
        | v4_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_22])).

fof(c_0_39,plain,(
    ! [X36] : m1_subset_1(k6_relat_1(X36),k1_zfmisc_1(k2_zfmisc_1(X36,X36))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

fof(c_0_40,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_41,plain,(
    ! [X32,X33,X34,X35] :
      ( ( ~ r2_relset_1(X32,X33,X34,X35)
        | X34 = X35
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X34 != X35
        | r2_relset_1(X32,X33,X34,X35)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_42,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0) = k5_relat_1(X3,esk4_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_46,plain,(
    ! [X37,X38,X39,X40,X41,X42] :
      ( ( v1_funct_1(k1_partfun1(X37,X38,X39,X40,X41,X42))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( m1_subset_1(k1_partfun1(X37,X38,X39,X40,X41,X42),k1_zfmisc_1(k2_zfmisc_1(X37,X40)))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
        | ~ v1_funct_1(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_47,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,esk3_0)),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_49,plain,(
    ! [X22] :
      ( ( k5_relat_1(X22,k2_funct_1(X22)) = k6_relat_1(k1_relat_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k5_relat_1(k2_funct_1(X22),X22) = k6_relat_1(k2_relat_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_50,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_28]),c_0_28])).

cnf(c_0_54,negated_conjecture,
    ( k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

fof(c_0_56,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X13,X14),X15) = k5_relat_1(X13,k5_relat_1(X14,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

fof(c_0_57,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(k1_relat_1(X18),X17)
      | k5_relat_1(k6_relat_1(X17),X18) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

fof(c_0_58,plain,(
    ! [X21] :
      ( ( k2_relat_1(X21) = k1_relat_1(k2_funct_1(X21))
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( k1_relat_1(X21) = k2_relat_1(k2_funct_1(X21))
        | ~ v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_59,negated_conjecture,
    ( v4_relat_1(k5_relat_1(X1,esk3_0),k1_relat_1(X1))
    | ~ v1_relat_1(k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_60,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_63,plain,(
    ! [X20] :
      ( ( v1_relat_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( v1_funct_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_67,plain,
    ( X1 = k6_relat_1(X2)
    | ~ r2_relset_1(X2,X2,X1,k6_relat_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_50])).

cnf(c_0_68,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_35])])).

cnf(c_0_70,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_71,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,negated_conjecture,
    ( v4_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k1_relat_1(k2_funct_1(esk3_0)))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62]),c_0_45]),c_0_38])])).

cnf(c_0_74,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_75,plain,(
    ! [X16] :
      ( k1_relat_1(k6_relat_1(X16)) = X16
      & k2_relat_1(k6_relat_1(X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])])).

fof(c_0_77,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_78,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_22])).

cnf(c_0_79,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_44]),c_0_54]),c_0_45])])).

cnf(c_0_81,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),X2) = k5_relat_1(X1,k5_relat_1(esk3_0,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_38])).

cnf(c_0_82,plain,
    ( k5_relat_1(k6_relat_1(X1),k2_funct_1(X2)) = k2_funct_1(X2)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,negated_conjecture,
    ( v4_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k1_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_45]),c_0_38])])).

cnf(c_0_84,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk2_0),esk4_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_76]),c_0_66])])).

cnf(c_0_86,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_78]),c_0_38])])).

cnf(c_0_88,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk3_0,X1)),k1_relat_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_90,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_60]),c_0_62]),c_0_45]),c_0_38])])).

cnf(c_0_91,plain,
    ( k5_relat_1(k6_relat_1(X1),k2_funct_1(X2)) = k2_funct_1(X2)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_74])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_83]),c_0_84]),c_0_61])])).

cnf(c_0_93,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0) = k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_66])).

cnf(c_0_94,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_85,c_0_28])).

cnf(c_0_95,negated_conjecture,
    ( esk1_0 = k1_relat_1(esk3_0)
    | ~ r1_tarski(esk1_0,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( esk1_0 = k1_relat_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_88])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk3_0,esk4_0)),k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_66])).

cnf(c_0_98,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_74]),c_0_45]),c_0_38])])).

cnf(c_0_99,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(esk3_0))),k2_funct_1(esk3_0)) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_62]),c_0_45]),c_0_38])])).

cnf(c_0_100,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = esk4_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_60]),c_0_94]),c_0_62]),c_0_45]),c_0_38])])).

cnf(c_0_101,negated_conjecture,
    ( k1_relat_1(k5_relat_1(esk3_0,esk4_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_96]),c_0_97])])).

cnf(c_0_102,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k2_funct_1(X1))) = k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_74])).

cnf(c_0_103,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_104,negated_conjecture,
    ( k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(esk3_0)) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_72]),c_0_62]),c_0_45]),c_0_38])])).

cnf(c_0_105,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_74]),c_0_45]),c_0_38])])).

cnf(c_0_106,negated_conjecture,
    ( k5_relat_1(esk3_0,esk4_0) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88,c_0_96]),c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0))) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104]),c_0_45]),c_0_38]),c_0_62])])).

cnf(c_0_108,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_109,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_108]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:56:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.76/0.94  # AutoSched0-Mode selected heuristic H_____042_B03_F1_AE_Q4_SP_S2S
% 0.76/0.94  # and selection function SelectNewComplexAHP.
% 0.76/0.94  #
% 0.76/0.94  # Preprocessing time       : 0.048 s
% 0.76/0.94  
% 0.76/0.94  # Proof found!
% 0.76/0.94  # SZS status Theorem
% 0.76/0.94  # SZS output start CNFRefutation
% 0.76/0.94  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 0.76/0.94  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.76/0.94  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.76/0.94  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.76/0.94  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.76/0.94  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.76/0.94  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.76/0.94  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.76/0.94  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.76/0.94  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.76/0.94  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.76/0.94  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.76/0.94  fof(t55_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 0.76/0.94  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 0.76/0.94  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.76/0.94  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.76/0.94  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.76/0.94  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.76/0.94  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 0.76/0.94  fof(c_0_19, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.76/0.94  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.76/0.94  cnf(c_0_21, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.76/0.94  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.76/0.94  cnf(c_0_23, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.76/0.94  fof(c_0_24, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.76/0.94  fof(c_0_25, plain, ![X49]:k6_partfun1(X49)=k6_relat_1(X49), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.76/0.94  fof(c_0_26, plain, ![X43, X44, X45, X46, X47, X48]:(~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|~v1_funct_1(X48)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k1_partfun1(X43,X44,X45,X46,X47,X48)=k5_relat_1(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.76/0.94  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.76/0.94  cnf(c_0_28, negated_conjecture, (esk2_0=k2_relat_1(esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.76/0.94  fof(c_0_29, plain, ![X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|r1_tarski(k1_relat_1(k5_relat_1(X11,X12)),k1_relat_1(X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.76/0.94  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.76/0.94  cnf(c_0_31, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.76/0.94  cnf(c_0_32, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.76/0.94  cnf(c_0_33, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.76/0.94  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk3_0),esk1_0)))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.76/0.94  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.76/0.94  fof(c_0_36, plain, ![X9, X10]:((~v4_relat_1(X10,X9)|r1_tarski(k1_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k1_relat_1(X10),X9)|v4_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.76/0.94  cnf(c_0_37, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.76/0.94  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_22])).
% 0.76/0.94  fof(c_0_39, plain, ![X36]:m1_subset_1(k6_relat_1(X36),k1_zfmisc_1(k2_zfmisc_1(X36,X36))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.76/0.94  fof(c_0_40, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.76/0.94  fof(c_0_41, plain, ![X32, X33, X34, X35]:((~r2_relset_1(X32,X33,X34,X35)|X34=X35|(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(X34!=X35|r2_relset_1(X32,X33,X34,X35)|(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.76/0.94  cnf(c_0_42, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.76/0.94  cnf(c_0_43, negated_conjecture, (k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0)=k5_relat_1(X3,esk4_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.76/0.94  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk3_0))))), inference(rw,[status(thm)],[c_0_22, c_0_28])).
% 0.76/0.94  cnf(c_0_45, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.76/0.94  fof(c_0_46, plain, ![X37, X38, X39, X40, X41, X42]:((v1_funct_1(k1_partfun1(X37,X38,X39,X40,X41,X42))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(m1_subset_1(k1_partfun1(X37,X38,X39,X40,X41,X42),k1_zfmisc_1(k2_zfmisc_1(X37,X40)))|(~v1_funct_1(X41)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|~v1_funct_1(X42)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.76/0.94  cnf(c_0_47, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.76/0.94  cnf(c_0_48, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(X1,esk3_0)),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.76/0.94  fof(c_0_49, plain, ![X22]:((k5_relat_1(X22,k2_funct_1(X22))=k6_relat_1(k1_relat_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k5_relat_1(k2_funct_1(X22),X22)=k6_relat_1(k2_relat_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.76/0.94  cnf(c_0_50, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.76/0.94  cnf(c_0_51, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.76/0.94  cnf(c_0_52, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.76/0.94  cnf(c_0_53, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_28]), c_0_28])).
% 0.76/0.94  cnf(c_0_54, negated_conjecture, (k1_partfun1(esk1_0,k2_relat_1(esk3_0),k2_relat_1(esk3_0),esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.76/0.94  cnf(c_0_55, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.76/0.94  fof(c_0_56, plain, ![X13, X14, X15]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|(~v1_relat_1(X15)|k5_relat_1(k5_relat_1(X13,X14),X15)=k5_relat_1(X13,k5_relat_1(X14,X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).
% 0.76/0.94  fof(c_0_57, plain, ![X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(k1_relat_1(X18),X17)|k5_relat_1(k6_relat_1(X17),X18)=X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.76/0.94  fof(c_0_58, plain, ![X21]:((k2_relat_1(X21)=k1_relat_1(k2_funct_1(X21))|~v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(k1_relat_1(X21)=k2_relat_1(k2_funct_1(X21))|~v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.76/0.94  cnf(c_0_59, negated_conjecture, (v4_relat_1(k5_relat_1(X1,esk3_0),k1_relat_1(X1))|~v1_relat_1(k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.76/0.94  cnf(c_0_60, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.76/0.94  cnf(c_0_61, plain, (v1_relat_1(k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_30, c_0_50])).
% 0.76/0.94  cnf(c_0_62, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.76/0.94  fof(c_0_63, plain, ![X20]:((v1_relat_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(v1_funct_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.76/0.94  cnf(c_0_64, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.76/0.94  cnf(c_0_65, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_27])).
% 0.76/0.94  cnf(c_0_66, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 0.76/0.94  cnf(c_0_67, plain, (X1=k6_relat_1(X2)|~r2_relset_1(X2,X2,X1,k6_relat_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(spm,[status(thm)],[c_0_52, c_0_50])).
% 0.76/0.94  cnf(c_0_68, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.76/0.94  cnf(c_0_69, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,k2_relat_1(esk3_0),esk1_0,X3,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_34]), c_0_35])])).
% 0.76/0.94  cnf(c_0_70, plain, (k5_relat_1(k5_relat_1(X1,X2),X3)=k5_relat_1(X1,k5_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.76/0.94  cnf(c_0_71, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.76/0.94  cnf(c_0_72, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.76/0.94  cnf(c_0_73, negated_conjecture, (v4_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k1_relat_1(k2_funct_1(esk3_0)))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62]), c_0_45]), c_0_38])])).
% 0.76/0.94  cnf(c_0_74, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.76/0.94  fof(c_0_75, plain, ![X16]:(k1_relat_1(k6_relat_1(X16))=X16&k2_relat_1(k6_relat_1(X16))=X16), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.76/0.94  cnf(c_0_76, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])])).
% 0.76/0.94  fof(c_0_77, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.76/0.94  cnf(c_0_78, negated_conjecture, (v4_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_51, c_0_22])).
% 0.76/0.94  cnf(c_0_79, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.76/0.94  cnf(c_0_80, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_44]), c_0_54]), c_0_45])])).
% 0.76/0.94  cnf(c_0_81, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),X2)=k5_relat_1(X1,k5_relat_1(esk3_0,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_70, c_0_38])).
% 0.76/0.94  cnf(c_0_82, plain, (k5_relat_1(k6_relat_1(X1),k2_funct_1(X2))=k2_funct_1(X2)|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_relat_1(k2_funct_1(X2))|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.76/0.94  cnf(c_0_83, negated_conjecture, (v4_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k1_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_45]), c_0_38])])).
% 0.76/0.94  cnf(c_0_84, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.76/0.94  cnf(c_0_85, negated_conjecture, (k5_relat_1(k6_relat_1(esk2_0),esk4_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_76]), c_0_66])])).
% 0.76/0.94  cnf(c_0_86, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.76/0.94  cnf(c_0_87, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_78]), c_0_38])])).
% 0.76/0.94  cnf(c_0_88, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80])])).
% 0.76/0.94  cnf(c_0_89, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk3_0,X1)),k1_relat_1(esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.76/0.94  cnf(c_0_90, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_60]), c_0_62]), c_0_45]), c_0_38])])).
% 0.76/0.94  cnf(c_0_91, plain, (k5_relat_1(k6_relat_1(X1),k2_funct_1(X2))=k2_funct_1(X2)|~v2_funct_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)), inference(spm,[status(thm)],[c_0_82, c_0_74])).
% 0.76/0.94  cnf(c_0_92, negated_conjecture, (r1_tarski(k2_relat_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_83]), c_0_84]), c_0_61])])).
% 0.76/0.94  cnf(c_0_93, negated_conjecture, (k5_relat_1(k5_relat_1(X1,esk3_0),esk4_0)=k5_relat_1(X1,k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_81, c_0_66])).
% 0.76/0.94  cnf(c_0_94, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),esk4_0)=esk4_0), inference(rw,[status(thm)],[c_0_85, c_0_28])).
% 0.76/0.94  cnf(c_0_95, negated_conjecture, (esk1_0=k1_relat_1(esk3_0)|~r1_tarski(esk1_0,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.76/0.94  cnf(c_0_96, negated_conjecture, (esk1_0=k1_relat_1(k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_84, c_0_88])).
% 0.76/0.94  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk3_0,esk4_0)),k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_89, c_0_66])).
% 0.76/0.94  cnf(c_0_98, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,X1))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_74]), c_0_45]), c_0_38])])).
% 0.76/0.94  cnf(c_0_99, negated_conjecture, (k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(esk3_0))),k2_funct_1(esk3_0))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_62]), c_0_45]), c_0_38])])).
% 0.76/0.94  cnf(c_0_100, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=esk4_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_60]), c_0_94]), c_0_62]), c_0_45]), c_0_38])])).
% 0.76/0.94  cnf(c_0_101, negated_conjecture, (k1_relat_1(k5_relat_1(esk3_0,esk4_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_96]), c_0_97])])).
% 0.76/0.94  cnf(c_0_102, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,k2_funct_1(X1)))=k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_98, c_0_74])).
% 0.76/0.94  cnf(c_0_103, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.76/0.94  cnf(c_0_104, negated_conjecture, (k5_relat_1(k6_relat_1(k2_relat_1(esk3_0)),k2_funct_1(esk3_0))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_72]), c_0_62]), c_0_45]), c_0_38])])).
% 0.76/0.94  cnf(c_0_105, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k5_relat_1(esk3_0,esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_74]), c_0_45]), c_0_38])])).
% 0.76/0.94  cnf(c_0_106, negated_conjecture, (k5_relat_1(esk3_0,esk4_0)=k6_relat_1(k1_relat_1(esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_88, c_0_96]), c_0_101])).
% 0.76/0.94  cnf(c_0_107, negated_conjecture, (k5_relat_1(k2_funct_1(esk3_0),k6_relat_1(k1_relat_1(esk3_0)))=k2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104]), c_0_45]), c_0_38]), c_0_62])])).
% 0.76/0.94  cnf(c_0_108, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.76/0.94  cnf(c_0_109, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_108]), ['proof']).
% 0.76/0.94  # SZS output end CNFRefutation
% 0.76/0.94  # Proof object total steps             : 110
% 0.76/0.94  # Proof object clause steps            : 73
% 0.76/0.94  # Proof object formula steps           : 37
% 0.76/0.94  # Proof object conjectures             : 53
% 0.76/0.94  # Proof object clause conjectures      : 50
% 0.76/0.94  # Proof object formula conjectures     : 3
% 0.76/0.94  # Proof object initial clauses used    : 27
% 0.76/0.94  # Proof object initial formulas used   : 18
% 0.76/0.94  # Proof object generating inferences   : 36
% 0.76/0.94  # Proof object simplifying inferences  : 73
% 0.76/0.94  # Training examples: 0 positive, 0 negative
% 0.76/0.94  # Parsed axioms                        : 19
% 0.76/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.76/0.94  # Initial clauses                      : 40
% 0.76/0.94  # Removed in clause preprocessing      : 1
% 0.76/0.94  # Initial clauses in saturation        : 39
% 0.76/0.94  # Processed clauses                    : 4883
% 0.76/0.94  # ...of these trivial                  : 345
% 0.76/0.94  # ...subsumed                          : 2732
% 0.76/0.94  # ...remaining for further processing  : 1806
% 0.76/0.94  # Other redundant clauses eliminated   : 3
% 0.76/0.94  # Clauses deleted for lack of memory   : 0
% 0.76/0.94  # Backward-subsumed                    : 103
% 0.76/0.94  # Backward-rewritten                   : 516
% 0.76/0.94  # Generated clauses                    : 37037
% 0.76/0.94  # ...of the previous two non-trivial   : 33570
% 0.76/0.94  # Contextual simplify-reflections      : 0
% 0.76/0.94  # Paramodulations                      : 37034
% 0.76/0.94  # Factorizations                       : 0
% 0.76/0.94  # Equation resolutions                 : 3
% 0.76/0.94  # Propositional unsat checks           : 0
% 0.76/0.94  #    Propositional check models        : 0
% 0.76/0.94  #    Propositional check unsatisfiable : 0
% 0.76/0.94  #    Propositional clauses             : 0
% 0.76/0.94  #    Propositional clauses after purity: 0
% 0.76/0.94  #    Propositional unsat core size     : 0
% 0.76/0.94  #    Propositional preprocessing time  : 0.000
% 0.76/0.94  #    Propositional encoding time       : 0.000
% 0.76/0.94  #    Propositional solver time         : 0.000
% 0.76/0.94  #    Success case prop preproc time    : 0.000
% 0.76/0.94  #    Success case prop encoding time   : 0.000
% 0.76/0.94  #    Success case prop solver time     : 0.000
% 0.76/0.94  # Current number of processed clauses  : 1184
% 0.76/0.94  #    Positive orientable unit clauses  : 201
% 0.76/0.94  #    Positive unorientable unit clauses: 0
% 0.76/0.94  #    Negative unit clauses             : 3
% 0.76/0.94  #    Non-unit-clauses                  : 980
% 0.76/0.94  # Current number of unprocessed clauses: 28637
% 0.76/0.94  # ...number of literals in the above   : 115152
% 0.76/0.94  # Current number of archived formulas  : 0
% 0.76/0.94  # Current number of archived clauses   : 620
% 0.76/0.94  # Clause-clause subsumption calls (NU) : 93603
% 0.76/0.94  # Rec. Clause-clause subsumption calls : 74418
% 0.76/0.94  # Non-unit clause-clause subsumptions  : 2835
% 0.76/0.94  # Unit Clause-clause subsumption calls : 3905
% 0.76/0.94  # Rewrite failures with RHS unbound    : 0
% 0.76/0.94  # BW rewrite match attempts            : 1339
% 0.76/0.94  # BW rewrite match successes           : 34
% 0.76/0.94  # Condensation attempts                : 0
% 0.76/0.94  # Condensation successes               : 0
% 0.76/0.94  # Termbank termtop insertions          : 1152547
% 0.76/0.94  
% 0.76/0.94  # -------------------------------------------------
% 0.76/0.94  # User time                : 0.590 s
% 0.76/0.94  # System time              : 0.023 s
% 0.76/0.94  # Total time               : 0.613 s
% 0.76/0.94  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
