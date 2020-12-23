%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:00 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  123 (1417 expanded)
%              Number of clauses        :   84 ( 519 expanded)
%              Number of leaves         :   19 ( 336 expanded)
%              Depth                    :   17
%              Number of atoms          :  494 (10190 expanded)
%              Number of equality atoms :  131 (3239 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   40 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

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

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t29_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X1)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))
           => ( v2_funct_1(X3)
              & v2_funct_2(X4,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(t48_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(k5_relat_1(X2,X1))
              & k2_relat_1(X2) = k1_relat_1(X1) )
           => ( v2_funct_1(X2)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

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

fof(t30_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
              & k2_relset_1(X1,X2,X4) = X2 )
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | ( v2_funct_1(X4)
                & v2_funct_1(X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t63_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
           => X2 = k2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(c_0_19,negated_conjecture,(
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

fof(c_0_20,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | v1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( v1_funct_1(k1_partfun1(X33,X34,X35,X36,X37,X38))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( m1_subset_1(k1_partfun1(X33,X34,X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(X33,X36)))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_23,plain,(
    ! [X55,X56,X57] :
      ( ( k5_relat_1(X57,k2_funct_1(X57)) = k6_partfun1(X55)
        | X56 = k1_xboole_0
        | k2_relset_1(X55,X56,X57) != X56
        | ~ v2_funct_1(X57)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( k5_relat_1(k2_funct_1(X57),X57) = k6_partfun1(X56)
        | X56 = k1_xboole_0
        | k2_relset_1(X55,X56,X57) != X56
        | ~ v2_funct_1(X57)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X56)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_24,plain,(
    ! [X45] : k6_partfun1(X45) = k6_relat_1(X45) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_25,plain,(
    ! [X14] :
      ( ( k5_relat_1(X14,k2_funct_1(X14)) = k6_relat_1(k1_relat_1(X14))
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( k5_relat_1(k2_funct_1(X14),X14) = k6_relat_1(k2_relat_1(X14))
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ~ v1_funct_1(X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_partfun1(X39,X40,X41,X42,X43,X44) = k5_relat_1(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_31,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_29])])).

cnf(c_0_39,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X9] :
      ( k1_relat_1(k6_relat_1(X9)) = X9
      & k2_relat_1(k6_relat_1(X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_41,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29]),c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_46,plain,(
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

cnf(c_0_47,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_48,plain,(
    ! [X30] : m1_subset_1(k6_relat_1(X30),k1_zfmisc_1(k2_zfmisc_1(X30,X30))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,esk4_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3) = k5_relat_1(esk3_0,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_29])])).

fof(c_0_53,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ r1_tarski(k1_relat_1(X11),X10)
      | k5_relat_1(k6_relat_1(X10),X11) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_54,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk3_0)) = k6_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_27]),c_0_34]),c_0_29])]),c_0_45])).

fof(c_0_56,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_59,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_29])).

fof(c_0_61,plain,(
    ! [X46,X47,X48,X49] :
      ( ( v2_funct_1(X48)
        | ~ r2_relset_1(X46,X46,k1_partfun1(X46,X47,X47,X46,X48,X49),k6_partfun1(X46))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X46)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( v2_funct_2(X49,X46)
        | ~ r2_relset_1(X46,X46,k1_partfun1(X46,X47,X47,X46,X48,X49),k6_partfun1(X46))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X46)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).

fof(c_0_62,plain,(
    ! [X12,X13] :
      ( ( v2_funct_1(X13)
        | ~ v2_funct_1(k5_relat_1(X13,X12))
        | k2_relat_1(X13) != k1_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( v2_funct_1(X12)
        | ~ v2_funct_1(k5_relat_1(X13,X12))
        | k2_relat_1(X13) != k1_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_37])])).

cnf(c_0_65,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_54])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0) = k6_relat_1(esk1_0)
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

fof(c_0_70,plain,(
    ! [X31,X32] :
      ( ( ~ v2_funct_2(X32,X31)
        | k2_relat_1(X32) = X31
        | ~ v1_relat_1(X32)
        | ~ v5_relat_1(X32,X31) )
      & ( k2_relat_1(X32) != X31
        | v2_funct_2(X32,X31)
        | ~ v1_relat_1(X32)
        | ~ v5_relat_1(X32,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

fof(c_0_71,plain,(
    ! [X20,X21,X22] :
      ( ( v4_relat_1(X22,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v5_relat_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_72,plain,
    ( v2_funct_2(X1,X2)
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_partfun1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_73,plain,(
    ! [X50,X51,X52,X53,X54] :
      ( ( v2_funct_1(X53)
        | X52 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X50,X51,X51,X52,X53,X54))
        | k2_relset_1(X50,X51,X53) != X51
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X50,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( v2_funct_1(X54)
        | X52 = k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X50,X51,X51,X52,X53,X54))
        | k2_relset_1(X50,X51,X53) != X51
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X50,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( v2_funct_1(X53)
        | X51 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X50,X51,X51,X52,X53,X54))
        | k2_relset_1(X50,X51,X53) != X51
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X50,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) )
      & ( v2_funct_1(X54)
        | X51 != k1_xboole_0
        | ~ v2_funct_1(k1_partfun1(X50,X51,X51,X52,X53,X54))
        | k2_relset_1(X50,X51,X53) != X51
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X51,X52)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X50,X51)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).

cnf(c_0_74,plain,
    ( v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,X2))
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk3_0) = esk3_0
    | ~ r1_tarski(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_35])])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0)
    | ~ m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_64]),c_0_64])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_27]),c_0_64])).

fof(c_0_80,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k2_relset_1(X23,X24,X25) = k2_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_81,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_51])).

cnf(c_0_83,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_84,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_relat_1(X2)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_32])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_86,plain,
    ( v2_funct_1(X1)
    | X2 = k1_xboole_0
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))
    | k2_relset_1(X3,X4,X5) != X4
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0))
    | k2_relat_1(k5_relat_1(esk3_0,esk4_0)) != k1_relat_1(X1)
    | ~ v2_funct_1(k5_relat_1(k5_relat_1(esk3_0,esk4_0),X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k5_relat_1(esk3_0,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_88,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk1_0),esk3_0) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_89,negated_conjecture,
    ( k6_relat_1(esk1_0) = k5_relat_1(esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79])])).

cnf(c_0_90,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( k2_relat_1(esk4_0) = X1
    | ~ v2_funct_2(esk4_0,X1)
    | ~ v5_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( v5_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_51])).

cnf(c_0_93,negated_conjecture,
    ( v2_funct_2(esk4_0,esk1_0)
    | ~ v1_funct_2(X1,esk1_0,esk2_0)
    | ~ r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,X1,esk4_0),k6_relat_1(esk1_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_51]),c_0_85]),c_0_37])])).

cnf(c_0_94,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_58,c_0_64])).

cnf(c_0_95,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_funct_1(esk4_0)
    | k2_relset_1(X2,X3,X4) != X3
    | ~ v1_funct_2(esk4_0,X3,X1)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(k1_partfun1(X2,X3,X3,X1,X4,esk4_0))
    | ~ v1_funct_1(X4) ),
    inference(spm,[status(thm)],[c_0_86,c_0_37])).

cnf(c_0_96,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0))
    | k2_relat_1(k5_relat_1(esk3_0,esk4_0)) != esk1_0
    | ~ v2_funct_1(k5_relat_1(k5_relat_1(esk3_0,esk4_0),esk3_0))
    | ~ v1_relat_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_35]),c_0_66]),c_0_29])])).

cnf(c_0_97,negated_conjecture,
    ( v1_relat_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_79])).

cnf(c_0_98,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk3_0,esk4_0),esk3_0) = esk3_0 ),
    inference(rw,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_99,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_100,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_51])).

cnf(c_0_101,negated_conjecture,
    ( esk1_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_102,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0
    | ~ v2_funct_2(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( v2_funct_2(esk4_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_29]),c_0_44]),c_0_64]),c_0_94]),c_0_27])])).

cnf(c_0_104,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_funct_1(esk4_0)
    | k2_relset_1(X2,X3,esk3_0) != X3
    | ~ v1_funct_2(esk4_0,X3,X1)
    | ~ v1_funct_2(esk3_0,X2,X3)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(k1_partfun1(X2,X3,X3,X1,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_29])).

cnf(c_0_105,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0))
    | k2_relat_1(k5_relat_1(esk3_0,esk4_0)) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])]),c_0_98]),c_0_34])])).

cnf(c_0_106,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk3_0,esk4_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_89])).

cnf(c_0_107,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0)
    | k2_relat_1(esk4_0) != esk1_0
    | ~ v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_100]),c_0_85]),c_0_51]),c_0_37])]),c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_103])])).

cnf(c_0_109,negated_conjecture,
    ( X1 = k1_xboole_0
    | v2_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk2_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,X1,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_44]),c_0_42]),c_0_27])])).

cnf(c_0_110,negated_conjecture,
    ( v2_funct_1(k5_relat_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_106])])).

fof(c_0_111,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ v1_relat_1(X16)
      | ~ v1_funct_1(X16)
      | ~ v2_funct_1(X15)
      | k2_relat_1(X15) != k1_relat_1(X16)
      | k5_relat_1(X15,X16) != k6_relat_1(k1_relat_1(X15))
      | X16 = k2_funct_1(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).

cnf(c_0_112,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108])])).

cnf(c_0_113,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_51]),c_0_85]),c_0_64]),c_0_110])]),c_0_101])).

cnf(c_0_114,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_115,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_27]),c_0_42])).

cnf(c_0_116,negated_conjecture,
    ( k5_relat_1(esk4_0,k2_funct_1(esk4_0)) = k6_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113])])).

cnf(c_0_117,negated_conjecture,
    ( X1 = k2_funct_1(esk3_0)
    | k5_relat_1(esk3_0,X1) != k6_relat_1(esk1_0)
    | k1_relat_1(X1) != esk2_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_35]),c_0_115]),c_0_34]),c_0_29])]),c_0_66])).

cnf(c_0_118,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk4_0)) = k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_113]),c_0_37]),c_0_82])]),c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( X1 = k2_funct_1(esk3_0)
    | k5_relat_1(esk3_0,X1) != k5_relat_1(esk3_0,esk4_0)
    | k1_relat_1(X1) != esk2_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_117,c_0_89])).

cnf(c_0_120,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_118]),c_0_54])).

cnf(c_0_121,negated_conjecture,
    ( esk4_0 != k2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_37]),c_0_82])]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:08:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 1.07/1.26  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05EI
% 1.07/1.26  # and selection function SelectDivPreferIntoLits.
% 1.07/1.26  #
% 1.07/1.26  # Preprocessing time       : 0.029 s
% 1.07/1.26  # Presaturation interreduction done
% 1.07/1.26  
% 1.07/1.26  # Proof found!
% 1.07/1.26  # SZS status Theorem
% 1.07/1.26  # SZS output start CNFRefutation
% 1.07/1.26  fof(t36_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 1.07/1.26  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.07/1.26  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 1.07/1.26  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 1.07/1.26  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.07/1.26  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 1.07/1.26  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 1.07/1.26  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.07/1.26  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.07/1.26  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 1.07/1.26  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 1.07/1.26  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.07/1.26  fof(t29_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1))=>(v2_funct_1(X3)&v2_funct_2(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 1.07/1.26  fof(t48_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 1.07/1.26  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 1.07/1.26  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.07/1.26  fof(t30_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))&k2_relset_1(X1,X2,X4)=X2)=>((X3=k1_xboole_0&X2!=k1_xboole_0)|(v2_funct_1(X4)&v2_funct_1(X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 1.07/1.26  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.07/1.26  fof(t63_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X1)=k1_relat_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 1.07/1.26  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>(((k2_relset_1(X1,X2,X3)=X2&r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X4),k6_partfun1(X1)))&v2_funct_1(X3))=>(X1=k1_xboole_0|X2=k1_xboole_0|X4=k2_funct_1(X3)))))), inference(assume_negation,[status(cth)],[t36_funct_2])).
% 1.07/1.26  fof(c_0_20, plain, ![X17, X18, X19]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|v1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.07/1.26  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&(((k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0&r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0)))&v2_funct_1(esk3_0))&((esk1_0!=k1_xboole_0&esk2_0!=k1_xboole_0)&esk4_0!=k2_funct_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 1.07/1.26  fof(c_0_22, plain, ![X33, X34, X35, X36, X37, X38]:((v1_funct_1(k1_partfun1(X33,X34,X35,X36,X37,X38))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(m1_subset_1(k1_partfun1(X33,X34,X35,X36,X37,X38),k1_zfmisc_1(k2_zfmisc_1(X33,X36)))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 1.07/1.26  fof(c_0_23, plain, ![X55, X56, X57]:((k5_relat_1(X57,k2_funct_1(X57))=k6_partfun1(X55)|X56=k1_xboole_0|(k2_relset_1(X55,X56,X57)!=X56|~v2_funct_1(X57))|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&(k5_relat_1(k2_funct_1(X57),X57)=k6_partfun1(X56)|X56=k1_xboole_0|(k2_relset_1(X55,X56,X57)!=X56|~v2_funct_1(X57))|(~v1_funct_1(X57)|~v1_funct_2(X57,X55,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 1.07/1.26  fof(c_0_24, plain, ![X45]:k6_partfun1(X45)=k6_relat_1(X45), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 1.07/1.26  fof(c_0_25, plain, ![X14]:((k5_relat_1(X14,k2_funct_1(X14))=k6_relat_1(k1_relat_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(k5_relat_1(k2_funct_1(X14),X14)=k6_relat_1(k2_relat_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 1.07/1.26  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.07/1.26  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_28, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.07/1.26  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  fof(c_0_30, plain, ![X39, X40, X41, X42, X43, X44]:(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k1_partfun1(X39,X40,X41,X42,X43,X44)=k5_relat_1(X43,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 1.07/1.26  cnf(c_0_31, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.07/1.26  cnf(c_0_32, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.07/1.26  cnf(c_0_33, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.07/1.26  cnf(c_0_34, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 1.07/1.26  cnf(c_0_36, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.07/1.26  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_38, negated_conjecture, (v1_funct_1(k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_29])])).
% 1.07/1.26  cnf(c_0_39, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.07/1.26  fof(c_0_40, plain, ![X9]:(k1_relat_1(k6_relat_1(X9))=X9&k2_relat_1(k6_relat_1(X9))=X9), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.07/1.26  cnf(c_0_41, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 1.07/1.26  cnf(c_0_42, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_43, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(k1_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29]), c_0_35])])).
% 1.07/1.26  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_45, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  fof(c_0_46, plain, ![X26, X27, X28, X29]:((~r2_relset_1(X26,X27,X28,X29)|X28=X29|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(X28!=X29|r2_relset_1(X26,X27,X28,X29)|(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 1.07/1.26  cnf(c_0_47, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  fof(c_0_48, plain, ![X30]:m1_subset_1(k6_relat_1(X30),k1_zfmisc_1(k2_zfmisc_1(X30,X30))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 1.07/1.26  cnf(c_0_49, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.07/1.26  cnf(c_0_50, negated_conjecture, (v1_funct_1(k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,esk4_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 1.07/1.26  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_52, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,X1,X2,esk3_0,X3)=k5_relat_1(esk3_0,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_29])])).
% 1.07/1.26  fof(c_0_53, plain, ![X10, X11]:(~v1_relat_1(X11)|(~r1_tarski(k1_relat_1(X11),X10)|k5_relat_1(k6_relat_1(X10),X11)=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 1.07/1.26  cnf(c_0_54, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.07/1.26  cnf(c_0_55, negated_conjecture, (k6_relat_1(k1_relat_1(esk3_0))=k6_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_27]), c_0_34]), c_0_29])]), c_0_45])).
% 1.07/1.26  fof(c_0_56, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.07/1.26  cnf(c_0_57, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.07/1.26  cnf(c_0_58, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_47, c_0_32])).
% 1.07/1.26  cnf(c_0_59, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.07/1.26  cnf(c_0_60, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_49, c_0_29])).
% 1.07/1.26  fof(c_0_61, plain, ![X46, X47, X48, X49]:((v2_funct_1(X48)|~r2_relset_1(X46,X46,k1_partfun1(X46,X47,X47,X46,X48,X49),k6_partfun1(X46))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X46)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))&(v2_funct_2(X49,X46)|~r2_relset_1(X46,X46,k1_partfun1(X46,X47,X47,X46,X48,X49),k6_partfun1(X46))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X46)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46))))|(~v1_funct_1(X48)|~v1_funct_2(X48,X46,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_funct_2])])])])).
% 1.07/1.26  fof(c_0_62, plain, ![X12, X13]:((v2_funct_1(X13)|(~v2_funct_1(k5_relat_1(X13,X12))|k2_relat_1(X13)!=k1_relat_1(X12))|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(v2_funct_1(X12)|(~v2_funct_1(k5_relat_1(X13,X12))|k2_relat_1(X13)!=k1_relat_1(X12))|(~v1_relat_1(X13)|~v1_funct_1(X13))|(~v1_relat_1(X12)|~v1_funct_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).
% 1.07/1.26  cnf(c_0_63, negated_conjecture, (v1_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 1.07/1.26  cnf(c_0_64, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_51]), c_0_37])])).
% 1.07/1.26  cnf(c_0_65, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.07/1.26  cnf(c_0_66, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_54])).
% 1.07/1.26  cnf(c_0_67, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_56])).
% 1.07/1.26  cnf(c_0_68, negated_conjecture, (k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0)=k6_relat_1(esk1_0)|~m1_subset_1(k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 1.07/1.26  cnf(c_0_69, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,esk2_0,esk1_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk1_0)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_60, c_0_51])).
% 1.07/1.26  fof(c_0_70, plain, ![X31, X32]:((~v2_funct_2(X32,X31)|k2_relat_1(X32)=X31|(~v1_relat_1(X32)|~v5_relat_1(X32,X31)))&(k2_relat_1(X32)!=X31|v2_funct_2(X32,X31)|(~v1_relat_1(X32)|~v5_relat_1(X32,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 1.07/1.26  fof(c_0_71, plain, ![X20, X21, X22]:((v4_relat_1(X22,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(v5_relat_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.07/1.26  cnf(c_0_72, plain, (v2_funct_2(X1,X2)|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_partfun1(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.07/1.26  fof(c_0_73, plain, ![X50, X51, X52, X53, X54]:(((v2_funct_1(X53)|X52=k1_xboole_0|(~v2_funct_1(k1_partfun1(X50,X51,X51,X52,X53,X54))|k2_relset_1(X50,X51,X53)!=X51)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X50,X51)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&(v2_funct_1(X54)|X52=k1_xboole_0|(~v2_funct_1(k1_partfun1(X50,X51,X51,X52,X53,X54))|k2_relset_1(X50,X51,X53)!=X51)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X50,X51)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))))&((v2_funct_1(X53)|X51!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X50,X51,X51,X52,X53,X54))|k2_relset_1(X50,X51,X53)!=X51)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X50,X51)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))))&(v2_funct_1(X54)|X51!=k1_xboole_0|(~v2_funct_1(k1_partfun1(X50,X51,X51,X52,X53,X54))|k2_relset_1(X50,X51,X53)!=X51)|(~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X50,X51)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X50,X51))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_funct_2])])])])).
% 1.07/1.26  cnf(c_0_74, plain, (v2_funct_1(X1)|~v2_funct_1(k5_relat_1(X1,X2))|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.07/1.26  cnf(c_0_75, negated_conjecture, (v1_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(rw,[status(thm)],[c_0_63, c_0_64])).
% 1.07/1.26  cnf(c_0_76, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk3_0)=esk3_0|~r1_tarski(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_35])])).
% 1.07/1.26  cnf(c_0_77, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_67])).
% 1.07/1.26  cnf(c_0_78, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)|~m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_64]), c_0_64])).
% 1.07/1.26  cnf(c_0_79, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_27]), c_0_64])).
% 1.07/1.26  fof(c_0_80, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k2_relset_1(X23,X24,X25)=k2_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.07/1.26  cnf(c_0_81, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 1.07/1.26  cnf(c_0_82, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_51])).
% 1.07/1.26  cnf(c_0_83, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.07/1.26  cnf(c_0_84, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X1)|~v1_funct_2(X4,X2,X3)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~r2_relset_1(X2,X2,k1_partfun1(X2,X3,X3,X2,X4,X1),k6_relat_1(X2))), inference(rw,[status(thm)],[c_0_72, c_0_32])).
% 1.07/1.26  cnf(c_0_85, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_86, plain, (v2_funct_1(X1)|X2=k1_xboole_0|~v2_funct_1(k1_partfun1(X3,X4,X4,X2,X5,X1))|k2_relset_1(X3,X4,X5)!=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_73])).
% 1.07/1.26  cnf(c_0_87, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))|k2_relat_1(k5_relat_1(esk3_0,esk4_0))!=k1_relat_1(X1)|~v2_funct_1(k5_relat_1(k5_relat_1(esk3_0,esk4_0),X1))|~v1_funct_1(X1)|~v1_relat_1(k5_relat_1(esk3_0,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 1.07/1.26  cnf(c_0_88, negated_conjecture, (k5_relat_1(k6_relat_1(esk1_0),esk3_0)=esk3_0), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.07/1.26  cnf(c_0_89, negated_conjecture, (k6_relat_1(esk1_0)=k5_relat_1(esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79])])).
% 1.07/1.26  cnf(c_0_90, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 1.07/1.26  cnf(c_0_91, negated_conjecture, (k2_relat_1(esk4_0)=X1|~v2_funct_2(esk4_0,X1)|~v5_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.07/1.26  cnf(c_0_92, negated_conjecture, (v5_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_83, c_0_51])).
% 1.07/1.26  cnf(c_0_93, negated_conjecture, (v2_funct_2(esk4_0,esk1_0)|~v1_funct_2(X1,esk1_0,esk2_0)|~r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk2_0,esk2_0,esk1_0,X1,esk4_0),k6_relat_1(esk1_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_51]), c_0_85]), c_0_37])])).
% 1.07/1.26  cnf(c_0_94, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk4_0),k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_58, c_0_64])).
% 1.07/1.26  cnf(c_0_95, negated_conjecture, (X1=k1_xboole_0|v2_funct_1(esk4_0)|k2_relset_1(X2,X3,X4)!=X3|~v1_funct_2(esk4_0,X3,X1)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(k1_partfun1(X2,X3,X3,X1,X4,esk4_0))|~v1_funct_1(X4)), inference(spm,[status(thm)],[c_0_86, c_0_37])).
% 1.07/1.26  cnf(c_0_96, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))|k2_relat_1(k5_relat_1(esk3_0,esk4_0))!=esk1_0|~v2_funct_1(k5_relat_1(k5_relat_1(esk3_0,esk4_0),esk3_0))|~v1_relat_1(k5_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_35]), c_0_66]), c_0_29])])).
% 1.07/1.26  cnf(c_0_97, negated_conjecture, (v1_relat_1(k5_relat_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_26, c_0_79])).
% 1.07/1.26  cnf(c_0_98, negated_conjecture, (k5_relat_1(k5_relat_1(esk3_0,esk4_0),esk3_0)=esk3_0), inference(rw,[status(thm)],[c_0_88, c_0_89])).
% 1.07/1.26  cnf(c_0_99, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.07/1.26  cnf(c_0_100, negated_conjecture, (k2_relset_1(esk2_0,esk1_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_90, c_0_51])).
% 1.07/1.26  cnf(c_0_101, negated_conjecture, (esk1_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_102, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0|~v2_funct_2(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 1.07/1.26  cnf(c_0_103, negated_conjecture, (v2_funct_2(esk4_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_29]), c_0_44]), c_0_64]), c_0_94]), c_0_27])])).
% 1.07/1.26  cnf(c_0_104, negated_conjecture, (X1=k1_xboole_0|v2_funct_1(esk4_0)|k2_relset_1(X2,X3,esk3_0)!=X3|~v1_funct_2(esk4_0,X3,X1)|~v1_funct_2(esk3_0,X2,X3)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(k1_partfun1(X2,X3,X3,X1,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_95, c_0_29])).
% 1.07/1.26  cnf(c_0_105, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))|k2_relat_1(k5_relat_1(esk3_0,esk4_0))!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])]), c_0_98]), c_0_34])])).
% 1.07/1.26  cnf(c_0_106, negated_conjecture, (k2_relat_1(k5_relat_1(esk3_0,esk4_0))=esk1_0), inference(spm,[status(thm)],[c_0_99, c_0_89])).
% 1.07/1.26  cnf(c_0_107, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)|k2_relat_1(esk4_0)!=esk1_0|~v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_100]), c_0_85]), c_0_51]), c_0_37])]), c_0_101])).
% 1.07/1.26  cnf(c_0_108, negated_conjecture, (k2_relat_1(esk4_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_103])])).
% 1.07/1.26  cnf(c_0_109, negated_conjecture, (X1=k1_xboole_0|v2_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk2_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~v2_funct_1(k1_partfun1(esk1_0,esk2_0,esk2_0,X1,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_44]), c_0_42]), c_0_27])])).
% 1.07/1.26  cnf(c_0_110, negated_conjecture, (v2_funct_1(k5_relat_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_106])])).
% 1.07/1.26  fof(c_0_111, plain, ![X15, X16]:(~v1_relat_1(X15)|~v1_funct_1(X15)|(~v1_relat_1(X16)|~v1_funct_1(X16)|(~v2_funct_1(X15)|k2_relat_1(X15)!=k1_relat_1(X16)|k5_relat_1(X15,X16)!=k6_relat_1(k1_relat_1(X15))|X16=k2_funct_1(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).
% 1.07/1.26  cnf(c_0_112, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)|~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108])])).
% 1.07/1.26  cnf(c_0_113, negated_conjecture, (v2_funct_1(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_51]), c_0_85]), c_0_64]), c_0_110])]), c_0_101])).
% 1.07/1.26  cnf(c_0_114, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 1.07/1.26  cnf(c_0_115, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_27]), c_0_42])).
% 1.07/1.26  cnf(c_0_116, negated_conjecture, (k5_relat_1(esk4_0,k2_funct_1(esk4_0))=k6_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113])])).
% 1.07/1.26  cnf(c_0_117, negated_conjecture, (X1=k2_funct_1(esk3_0)|k5_relat_1(esk3_0,X1)!=k6_relat_1(esk1_0)|k1_relat_1(X1)!=esk2_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_35]), c_0_115]), c_0_34]), c_0_29])]), c_0_66])).
% 1.07/1.26  cnf(c_0_118, negated_conjecture, (k6_relat_1(k1_relat_1(esk4_0))=k6_relat_1(esk2_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_113]), c_0_37]), c_0_82])]), c_0_116])).
% 1.07/1.26  cnf(c_0_119, negated_conjecture, (X1=k2_funct_1(esk3_0)|k5_relat_1(esk3_0,X1)!=k5_relat_1(esk3_0,esk4_0)|k1_relat_1(X1)!=esk2_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_117, c_0_89])).
% 1.07/1.26  cnf(c_0_120, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_118]), c_0_54])).
% 1.07/1.26  cnf(c_0_121, negated_conjecture, (esk4_0!=k2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.07/1.26  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_37]), c_0_82])]), c_0_121]), ['proof']).
% 1.07/1.26  # SZS output end CNFRefutation
% 1.07/1.26  # Proof object total steps             : 123
% 1.07/1.26  # Proof object clause steps            : 84
% 1.07/1.26  # Proof object formula steps           : 39
% 1.07/1.26  # Proof object conjectures             : 64
% 1.07/1.26  # Proof object clause conjectures      : 61
% 1.07/1.26  # Proof object formula conjectures     : 3
% 1.07/1.26  # Proof object initial clauses used    : 32
% 1.07/1.26  # Proof object initial formulas used   : 19
% 1.07/1.26  # Proof object generating inferences   : 37
% 1.07/1.26  # Proof object simplifying inferences  : 86
% 1.07/1.26  # Training examples: 0 positive, 0 negative
% 1.07/1.26  # Parsed axioms                        : 19
% 1.07/1.26  # Removed by relevancy pruning/SinE    : 0
% 1.07/1.26  # Initial clauses                      : 44
% 1.07/1.26  # Removed in clause preprocessing      : 1
% 1.07/1.26  # Initial clauses in saturation        : 43
% 1.07/1.26  # Processed clauses                    : 2900
% 1.07/1.26  # ...of these trivial                  : 154
% 1.07/1.26  # ...subsumed                          : 50
% 1.07/1.26  # ...remaining for further processing  : 2696
% 1.07/1.26  # Other redundant clauses eliminated   : 80
% 1.07/1.26  # Clauses deleted for lack of memory   : 0
% 1.07/1.26  # Backward-subsumed                    : 0
% 1.07/1.26  # Backward-rewritten                   : 443
% 1.07/1.26  # Generated clauses                    : 66758
% 1.07/1.26  # ...of the previous two non-trivial   : 66923
% 1.07/1.26  # Contextual simplify-reflections      : 0
% 1.07/1.26  # Paramodulations                      : 66678
% 1.07/1.26  # Factorizations                       : 0
% 1.07/1.26  # Equation resolutions                 : 80
% 1.07/1.26  # Propositional unsat checks           : 0
% 1.07/1.26  #    Propositional check models        : 0
% 1.07/1.26  #    Propositional check unsatisfiable : 0
% 1.07/1.26  #    Propositional clauses             : 0
% 1.07/1.26  #    Propositional clauses after purity: 0
% 1.07/1.26  #    Propositional unsat core size     : 0
% 1.07/1.26  #    Propositional preprocessing time  : 0.000
% 1.07/1.26  #    Propositional encoding time       : 0.000
% 1.07/1.26  #    Propositional solver time         : 0.000
% 1.07/1.26  #    Success case prop preproc time    : 0.000
% 1.07/1.26  #    Success case prop encoding time   : 0.000
% 1.07/1.26  #    Success case prop solver time     : 0.000
% 1.07/1.26  # Current number of processed clauses  : 2205
% 1.07/1.26  #    Positive orientable unit clauses  : 1180
% 1.07/1.26  #    Positive unorientable unit clauses: 0
% 1.07/1.26  #    Negative unit clauses             : 3
% 1.07/1.26  #    Non-unit-clauses                  : 1022
% 1.07/1.26  # Current number of unprocessed clauses: 63681
% 1.07/1.26  # ...number of literals in the above   : 240637
% 1.07/1.26  # Current number of archived formulas  : 0
% 1.07/1.26  # Current number of archived clauses   : 486
% 1.07/1.26  # Clause-clause subsumption calls (NU) : 120669
% 1.07/1.26  # Rec. Clause-clause subsumption calls : 23883
% 1.07/1.26  # Non-unit clause-clause subsumptions  : 50
% 1.07/1.26  # Unit Clause-clause subsumption calls : 10187
% 1.07/1.26  # Rewrite failures with RHS unbound    : 0
% 1.07/1.26  # BW rewrite match attempts            : 89396
% 1.07/1.26  # BW rewrite match successes           : 97
% 1.07/1.26  # Condensation attempts                : 0
% 1.07/1.26  # Condensation successes               : 0
% 1.07/1.26  # Termbank termtop insertions          : 4459933
% 1.07/1.27  
% 1.07/1.27  # -------------------------------------------------
% 1.07/1.27  # User time                : 0.897 s
% 1.07/1.27  # System time              : 0.039 s
% 1.07/1.27  # Total time               : 0.936 s
% 1.07/1.27  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
