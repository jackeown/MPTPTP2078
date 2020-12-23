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
% DateTime   : Thu Dec  3 11:05:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  156 (19582 expanded)
%              Number of clauses        :  111 (7115 expanded)
%              Number of leaves         :   22 (4816 expanded)
%              Depth                    :   32
%              Number of atoms          :  554 (103073 expanded)
%              Number of equality atoms :  119 (5212 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t76_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_funct_2(X3,X1,X1)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
         => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)
              & v2_funct_1(X2) )
           => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t51_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
              & v2_funct_1(X1) )
           => r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

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

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(t44_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X2)
              & k5_relat_1(X1,X2) = X1 )
           => X2 = k6_relat_1(k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t66_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X2) )
           => k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ! [X3] :
            ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X1)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
           => ( ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)
                & v2_funct_1(X2) )
             => r2_relset_1(X1,X1,X3,k6_partfun1(X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_funct_2])).

fof(c_0_23,plain,(
    ! [X45,X46,X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k1_partfun1(X45,X46,X47,X48,X49,X50) = k5_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_25,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k1_relset_1(X29,X30,X31) = k1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_26,plain,(
    ! [X56,X57] :
      ( ~ v1_funct_1(X57)
      | ~ v1_funct_2(X57,X56,X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X56,X56)))
      | k1_relset_1(X56,X56,X57) = X56 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

cnf(c_0_27,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_35,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k2_relset_1(X32,X33,X34) = k2_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_36,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_37,plain,(
    ! [X13,X14] : v1_relat_1(k2_zfmisc_1(X13,X14)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_38,plain,(
    ! [X35,X36,X37,X38] :
      ( ( ~ r2_relset_1(X35,X36,X37,X38)
        | X37 = X38
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != X38
        | r2_relset_1(X35,X36,X37,X38)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

fof(c_0_39,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ( v1_funct_1(k1_partfun1(X39,X40,X41,X42,X43,X44))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( m1_subset_1(k1_partfun1(X39,X40,X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X39,X42)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_40,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,X1,X2,esk3_0,X3) = k5_relat_1(esk3_0,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

fof(c_0_41,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_42,plain,(
    ! [X11,X12] :
      ( ( ~ v5_relat_1(X12,X11)
        | r1_tarski(k2_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k2_relat_1(X12),X11)
        | v5_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_43,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | ~ v1_relat_1(X21)
      | ~ v1_funct_1(X21)
      | k2_relat_1(k5_relat_1(X21,X20)) != k2_relat_1(X20)
      | ~ v2_funct_1(X20)
      | r1_tarski(k1_relat_1(X20),k2_relat_1(X21)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_funct_1])])])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk2_0) = k1_relset_1(esk1_0,esk1_0,esk2_0) ),
    inference(pm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32,c_0_31]),c_0_33]),c_0_34])])).

cnf(c_0_46,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) = k5_relat_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40,c_0_31]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(k5_relat_1(X2,X1)) != k2_relat_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk2_0) = k2_relset_1(esk1_0,esk1_0,esk2_0) ),
    inference(pm,[status(thm)],[c_0_46,c_0_31])).

cnf(c_0_58,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_31]),c_0_48])])).

cnf(c_0_60,negated_conjecture,
    ( X1 = esk2_0
    | ~ r2_relset_1(esk1_0,esk1_0,X1,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(pm,[status(thm)],[c_0_49,c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_51]),c_0_34]),c_0_29]),c_0_31]),c_0_28])])).

cnf(c_0_62,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk2_0),esk2_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_51])).

fof(c_0_63,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_64,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_66,plain,
    ( k2_relat_1(X1) = X2
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(pm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_67,negated_conjecture,
    ( k2_relat_1(esk3_0) = k2_relset_1(esk1_0,esk1_0,esk3_0) ),
    inference(pm,[status(thm)],[c_0_46,c_0_28])).

cnf(c_0_68,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_28]),c_0_48])])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(X1))
    | k2_relat_1(k5_relat_1(X1,esk2_0)) != k2_relset_1(esk1_0,esk1_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_58]),c_0_34]),c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( k5_relat_1(esk3_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_71,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( v5_relat_1(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_73,plain,(
    ! [X22] :
      ( ( k2_relat_1(X22) = k1_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_relat_1(X22) = k2_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_75,plain,(
    ! [X55] :
      ( ( v1_funct_1(X55)
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) )
      & ( v1_funct_2(X55,k1_relat_1(X55),k2_relat_1(X55))
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) )
      & ( m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X55),k2_relat_1(X55))))
        | ~ v1_relat_1(X55)
        | ~ v1_funct_1(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

cnf(c_0_76,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk3_0) = X1
    | ~ v5_relat_1(esk3_0,X1)
    | ~ r1_tarski(X1,k2_relset_1(esk1_0,esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_67]),c_0_67]),c_0_68])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relset_1(esk1_0,esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69,c_0_70]),c_0_67]),c_0_57]),c_0_29]),c_0_68])])).

cnf(c_0_78,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(pm,[status(thm)],[c_0_71,c_0_28])).

cnf(c_0_79,plain,
    ( v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relset_1(esk1_0,esk1_0,esk3_0) ),
    inference(pm,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_82,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32,c_0_28]),c_0_74]),c_0_29])])).

fof(c_0_83,plain,(
    ! [X18,X19] :
      ( ( v2_funct_1(X19)
        | ~ v2_funct_1(k5_relat_1(X19,X18))
        | k2_relat_1(X19) != k1_relat_1(X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( v2_funct_1(X18)
        | ~ v2_funct_1(k5_relat_1(X19,X18))
        | k2_relat_1(X19) != k1_relat_1(X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_86,plain,
    ( v5_relat_1(k2_funct_1(X1),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

fof(c_0_88,plain,(
    ! [X15] :
      ( ( v1_relat_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( v1_funct_1(k2_funct_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_89,plain,
    ( v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,X2))
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relset_1(esk1_0,esk1_0,esk3_0),k2_relset_1(esk1_0,esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84,c_0_81]),c_0_29]),c_0_68])]),c_0_67])).

cnf(c_0_91,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_92,plain,
    ( k2_relat_1(X1) = k2_relat_1(X2)
    | ~ v5_relat_1(X1,k2_relat_1(X2))
    | ~ v5_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(pm,[status(thm)],[c_0_66,c_0_54])).

cnf(c_0_93,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk3_0),esk1_0)
    | ~ v2_funct_1(esk3_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86,c_0_87]),c_0_29]),c_0_68])])).

cnf(c_0_95,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | k2_relset_1(esk1_0,esk1_0,esk3_0) != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89,c_0_70]),c_0_58]),c_0_44]),c_0_45]),c_0_67]),c_0_34]),c_0_29]),c_0_59]),c_0_68])])).

fof(c_0_97,plain,(
    ! [X52,X53,X54] :
      ( ( v1_funct_1(k2_funct_1(X54))
        | ~ v2_funct_1(X54)
        | k2_relset_1(X52,X53,X54) != X53
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( v1_funct_2(k2_funct_1(X54),X53,X52)
        | ~ v2_funct_1(X54)
        | k2_relset_1(X52,X53,X54) != X53
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( m1_subset_1(k2_funct_1(X54),k1_zfmisc_1(k2_zfmisc_1(X53,X52)))
        | ~ v2_funct_1(X54)
        | k2_relset_1(X52,X53,X54) != X53
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X53)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relset_1(esk1_0,esk1_0,esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_90,c_0_82])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_relset_1(esk1_0,esk1_0,esk3_0),k2_relset_1(esk1_0,esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91,c_0_81]),c_0_29]),c_0_68])]),c_0_67])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(X1) = esk1_0
    | ~ v5_relat_1(esk3_0,k2_relat_1(X1))
    | ~ v5_relat_1(X1,esk1_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92,c_0_93]),c_0_67]),c_0_85]),c_0_68])])).

cnf(c_0_101,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk3_0),esk1_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_94,c_0_95]),c_0_29]),c_0_68])])).

cnf(c_0_102,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_85])])).

cnf(c_0_103,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( k2_relset_1(esk1_0,k2_relset_1(esk1_0,esk1_0,esk3_0),esk3_0) = k2_relset_1(esk1_0,esk1_0,esk3_0) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46,c_0_98]),c_0_67])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,k2_relset_1(esk1_0,esk1_0,esk3_0)) ),
    inference(rw,[status(thm)],[c_0_99,c_0_82])).

cnf(c_0_106,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_107,negated_conjecture,
    ( k2_relat_1(k2_funct_1(X1)) = esk1_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v5_relat_1(esk3_0,k1_relat_1(X1))
    | ~ v5_relat_1(k2_funct_1(X1),esk1_0)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_100,c_0_80])).

cnf(c_0_108,negated_conjecture,
    ( v5_relat_1(k2_funct_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_102])])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103,c_0_98]),c_0_29])]),c_0_104]),c_0_105])])).

cnf(c_0_110,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_111,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_84,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) = esk1_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107,c_0_87]),c_0_78]),c_0_102]),c_0_29]),c_0_108]),c_0_68])])).

cnf(c_0_113,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_102])])).

cnf(c_0_114,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),k2_relset_1(esk1_0,esk1_0,esk3_0),esk1_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_110,c_0_98]),c_0_104]),c_0_105]),c_0_29])])).

cnf(c_0_115,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111,c_0_112]),c_0_67]),c_0_85]),c_0_102]),c_0_113]),c_0_29]),c_0_68])])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_85]),c_0_102])])).

fof(c_0_117,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v1_funct_1(X16)
      | ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | k2_relat_1(X16) != k1_relat_1(X17)
      | k5_relat_1(X16,X17) != X16
      | X17 = k6_relat_1(k1_relat_1(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).

fof(c_0_118,plain,(
    ! [X23] :
      ( ( k5_relat_1(X23,k2_funct_1(X23)) = k6_relat_1(k1_relat_1(X23))
        | ~ v2_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( k5_relat_1(k2_funct_1(X23),X23) = k6_relat_1(k2_relat_1(X23))
        | ~ v2_funct_1(X23)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_119,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,k2_funct_1(esk3_0)) = esk1_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32,c_0_115]),c_0_116]),c_0_113])])).

cnf(c_0_120,plain,
    ( X2 = k6_relat_1(k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_121,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( k1_relset_1(esk1_0,esk1_0,k2_funct_1(esk3_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_119,c_0_95]),c_0_29]),c_0_68])])).

cnf(c_0_123,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(X1)
    | k6_relat_1(k1_relat_1(X1)) != X1
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_124,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = esk1_0
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30,c_0_115]),c_0_122])).

cnf(c_0_125,negated_conjecture,
    ( k2_funct_1(esk3_0) = k6_relat_1(esk1_0)
    | k1_relat_1(k2_funct_1(esk3_0)) != esk1_0
    | esk3_0 != k6_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_123,c_0_124]),c_0_67]),c_0_85]),c_0_81]),c_0_82]),c_0_102]),c_0_113]),c_0_29]),c_0_68])])).

cnf(c_0_126,negated_conjecture,
    ( k2_funct_1(esk3_0) = k6_relat_1(esk1_0)
    | esk3_0 != k6_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125,c_0_106]),c_0_67]),c_0_85]),c_0_102]),c_0_29]),c_0_68])])).

fof(c_0_127,plain,(
    ! [X51] : k6_partfun1(X51) = k6_relat_1(X51) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_128,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_129,negated_conjecture,
    ( k2_funct_1(esk3_0) = k6_relat_1(esk1_0)
    | esk3_0 != k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_126,c_0_95]),c_0_29]),c_0_68])])).

cnf(c_0_130,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_131,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_127])).

cnf(c_0_132,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,esk3_0,X1)
    | esk3_0 != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(pm,[status(thm)],[c_0_128,c_0_28])).

cnf(c_0_133,negated_conjecture,
    ( m1_subset_1(k6_relat_1(esk1_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | esk3_0 != k6_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_115,c_0_129])).

cnf(c_0_134,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_135,negated_conjecture,
    ( esk3_0 != k6_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_132,c_0_133]),c_0_134])).

cnf(c_0_136,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k5_relat_1(k2_funct_1(X2),X1) != k2_funct_1(X2)
    | k1_relat_1(X2) != k1_relat_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(k2_funct_1(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(k2_funct_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(pm,[status(thm)],[c_0_120,c_0_80])).

cnf(c_0_137,negated_conjecture,
    ( esk3_0 != k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_135,c_0_95]),c_0_29]),c_0_68])])).

fof(c_0_138,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ v2_funct_1(X24)
      | ~ v2_funct_1(X25)
      | k2_funct_1(k5_relat_1(X24,X25)) = k5_relat_1(k2_funct_1(X25),k2_funct_1(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).

cnf(c_0_139,negated_conjecture,
    ( k5_relat_1(k2_funct_1(X1),esk3_0) != k2_funct_1(X1)
    | k1_relat_1(X1) != esk1_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_136,c_0_87]),c_0_81]),c_0_82]),c_0_29]),c_0_68])]),c_0_137])).

cnf(c_0_140,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_141,plain,
    ( k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_138])).

cnf(c_0_142,negated_conjecture,
    ( k2_funct_1(esk3_0) != k6_relat_1(esk1_0)
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_139,c_0_140]),c_0_67]),c_0_85]),c_0_81]),c_0_82]),c_0_102]),c_0_113]),c_0_29]),c_0_68])])).

cnf(c_0_143,negated_conjecture,
    ( v1_funct_2(esk2_0,k1_relset_1(esk1_0,esk1_0,esk2_0),k2_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91,c_0_44]),c_0_34]),c_0_59])]),c_0_57])).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relset_1(esk1_0,esk1_0,esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84,c_0_56]),c_0_57]),c_0_34]),c_0_59])])).

cnf(c_0_145,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(X1))) = k2_funct_1(X1)
    | k1_relat_1(k2_funct_1(X1)) != k2_relat_1(k2_funct_1(X2))
    | k2_funct_1(k5_relat_1(X1,X2)) != k2_funct_1(X2)
    | ~ v2_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(k2_funct_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(k2_funct_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_120,c_0_141])).

cnf(c_0_146,negated_conjecture,
    ( k2_funct_1(esk3_0) != k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_142,c_0_95]),c_0_29]),c_0_68])])).

cnf(c_0_147,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,k2_relset_1(esk1_0,esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[c_0_143,c_0_45])).

cnf(c_0_148,negated_conjecture,
    ( k2_relset_1(esk1_0,k2_relset_1(esk1_0,esk1_0,esk2_0),esk2_0) = k2_relset_1(esk1_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46,c_0_144]),c_0_57])).

cnf(c_0_149,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) != k2_relat_1(k2_funct_1(X1))
    | k2_funct_1(k5_relat_1(esk3_0,X1)) != k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_145,c_0_124]),c_0_102]),c_0_113]),c_0_29]),c_0_68])]),c_0_146])).

cnf(c_0_150,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103,c_0_144]),c_0_147]),c_0_58]),c_0_34])]),c_0_148])])).

cnf(c_0_151,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk2_0)) != k1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_149,c_0_70]),c_0_58]),c_0_150]),c_0_34]),c_0_59])])).

cnf(c_0_152,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) != esk1_0
    | ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_151,c_0_80]),c_0_44]),c_0_45]),c_0_58]),c_0_34]),c_0_59])])).

cnf(c_0_153,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_152,c_0_106]),c_0_67]),c_0_85]),c_0_102]),c_0_29]),c_0_68])])).

cnf(c_0_154,negated_conjecture,
    ( ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_153,c_0_95]),c_0_29]),c_0_68])])).

cnf(c_0_155,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_154,c_0_95]),c_0_34]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.19/0.47  # and selection function NoSelection.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.039 s
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 0.19/0.47  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.19/0.47  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.47  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.19/0.47  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.47  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.47  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.47  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.47  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.19/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.47  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.47  fof(t51_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)&v2_funct_1(X1))=>r1_tarski(k1_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 0.19/0.47  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.47  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.47  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.47  fof(t48_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 0.19/0.47  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.47  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.47  fof(t44_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 0.19/0.47  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.19/0.47  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.47  fof(t66_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 0.19/0.47  fof(c_0_22, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.19/0.47  fof(c_0_23, plain, ![X45, X46, X47, X48, X49, X50]:(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k1_partfun1(X45,X46,X47,X48,X49,X50)=k5_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.19/0.47  fof(c_0_24, negated_conjecture, (((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)&v2_funct_1(esk2_0))&~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.47  fof(c_0_25, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k1_relset_1(X29,X30,X31)=k1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.47  fof(c_0_26, plain, ![X56, X57]:(~v1_funct_1(X57)|~v1_funct_2(X57,X56,X56)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X56,X56)))|k1_relset_1(X56,X56,X57)=X56), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.19/0.47  cnf(c_0_27, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.47  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.47  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_32, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.47  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  fof(c_0_35, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k2_relset_1(X32,X33,X34)=k2_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.47  fof(c_0_36, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.47  fof(c_0_37, plain, ![X13, X14]:v1_relat_1(k2_zfmisc_1(X13,X14)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.47  fof(c_0_38, plain, ![X35, X36, X37, X38]:((~r2_relset_1(X35,X36,X37,X38)|X37=X38|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(X37!=X38|r2_relset_1(X35,X36,X37,X38)|(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.47  fof(c_0_39, plain, ![X39, X40, X41, X42, X43, X44]:((v1_funct_1(k1_partfun1(X39,X40,X41,X42,X43,X44))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(m1_subset_1(k1_partfun1(X39,X40,X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X39,X42)))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.19/0.47  cnf(c_0_40, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,X1,X2,esk3_0,X3)=k5_relat_1(esk3_0,X3)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.19/0.47  fof(c_0_41, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.47  fof(c_0_42, plain, ![X11, X12]:((~v5_relat_1(X12,X11)|r1_tarski(k2_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k2_relat_1(X12),X11)|v5_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.47  fof(c_0_43, plain, ![X20, X21]:(~v1_relat_1(X20)|~v1_funct_1(X20)|(~v1_relat_1(X21)|~v1_funct_1(X21)|(k2_relat_1(k5_relat_1(X21,X20))!=k2_relat_1(X20)|~v2_funct_1(X20)|r1_tarski(k1_relat_1(X20),k2_relat_1(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t51_funct_1])])])).
% 0.19/0.47  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk2_0)=k1_relset_1(esk1_0,esk1_0,esk2_0)), inference(pm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.47  cnf(c_0_45, negated_conjecture, (k1_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32, c_0_31]), c_0_33]), c_0_34])])).
% 0.19/0.47  cnf(c_0_46, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_47, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_48, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.47  cnf(c_0_49, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.47  cnf(c_0_50, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.47  cnf(c_0_51, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)=k5_relat_1(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40, c_0_31]), c_0_34])])).
% 0.19/0.47  cnf(c_0_52, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_53, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.47  cnf(c_0_54, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.47  cnf(c_0_55, plain, (r1_tarski(k1_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(k5_relat_1(X2,X1))!=k2_relat_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.47  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk2_0)=esk1_0), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.47  cnf(c_0_57, negated_conjecture, (k2_relat_1(esk2_0)=k2_relset_1(esk1_0,esk1_0,esk2_0)), inference(pm,[status(thm)],[c_0_46, c_0_31])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_59, negated_conjecture, (v1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_31]), c_0_48])])).
% 0.19/0.47  cnf(c_0_60, negated_conjecture, (X1=esk2_0|~r2_relset_1(esk1_0,esk1_0,X1,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(pm,[status(thm)],[c_0_49, c_0_31])).
% 0.19/0.47  cnf(c_0_61, negated_conjecture, (m1_subset_1(k5_relat_1(esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_51]), c_0_34]), c_0_29]), c_0_31]), c_0_28])])).
% 0.19/0.47  cnf(c_0_62, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k5_relat_1(esk3_0,esk2_0),esk2_0)), inference(rw,[status(thm)],[c_0_52, c_0_51])).
% 0.19/0.47  fof(c_0_63, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.47  cnf(c_0_64, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.47  cnf(c_0_65, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.47  cnf(c_0_66, plain, (k2_relat_1(X1)=X2|~v5_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(pm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.47  cnf(c_0_67, negated_conjecture, (k2_relat_1(esk3_0)=k2_relset_1(esk1_0,esk1_0,esk3_0)), inference(pm,[status(thm)],[c_0_46, c_0_28])).
% 0.19/0.47  cnf(c_0_68, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_28]), c_0_48])])).
% 0.19/0.47  cnf(c_0_69, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(X1))|k2_relat_1(k5_relat_1(X1,esk2_0))!=k2_relset_1(esk1_0,esk1_0,esk2_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_58]), c_0_34]), c_0_59])])).
% 0.19/0.47  cnf(c_0_70, negated_conjecture, (k5_relat_1(esk3_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.19/0.47  cnf(c_0_71, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.47  cnf(c_0_72, plain, (v5_relat_1(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.47  fof(c_0_73, plain, ![X22]:((k2_relat_1(X22)=k1_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k1_relat_1(X22)=k2_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.47  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  fof(c_0_75, plain, ![X55]:(((v1_funct_1(X55)|(~v1_relat_1(X55)|~v1_funct_1(X55)))&(v1_funct_2(X55,k1_relat_1(X55),k2_relat_1(X55))|(~v1_relat_1(X55)|~v1_funct_1(X55))))&(m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X55),k2_relat_1(X55))))|(~v1_relat_1(X55)|~v1_funct_1(X55)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.47  cnf(c_0_76, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk3_0)=X1|~v5_relat_1(esk3_0,X1)|~r1_tarski(X1,k2_relset_1(esk1_0,esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_67]), c_0_67]), c_0_68])])).
% 0.19/0.47  cnf(c_0_77, negated_conjecture, (r1_tarski(esk1_0,k2_relset_1(esk1_0,esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69, c_0_70]), c_0_67]), c_0_57]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(pm,[status(thm)],[c_0_71, c_0_28])).
% 0.19/0.47  cnf(c_0_79, plain, (v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_72])).
% 0.19/0.47  cnf(c_0_80, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.47  cnf(c_0_81, negated_conjecture, (k1_relat_1(esk3_0)=k1_relset_1(esk1_0,esk1_0,esk3_0)), inference(pm,[status(thm)],[c_0_30, c_0_28])).
% 0.19/0.47  cnf(c_0_82, negated_conjecture, (k1_relset_1(esk1_0,esk1_0,esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32, c_0_28]), c_0_74]), c_0_29])])).
% 0.19/0.47  fof(c_0_83, plain, ![X18, X19]:((v2_funct_1(X19)|(~v2_funct_1(k5_relat_1(X19,X18))|k2_relat_1(X19)!=k1_relat_1(X18))|(~v1_relat_1(X19)|~v1_funct_1(X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(v2_funct_1(X18)|(~v2_funct_1(k5_relat_1(X19,X18))|k2_relat_1(X19)!=k1_relat_1(X18))|(~v1_relat_1(X19)|~v1_funct_1(X19))|(~v1_relat_1(X18)|~v1_funct_1(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).
% 0.19/0.47  cnf(c_0_84, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.47  cnf(c_0_85, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 0.19/0.47  cnf(c_0_86, plain, (v5_relat_1(k2_funct_1(X1),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_79, c_0_80])).
% 0.19/0.47  cnf(c_0_87, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.47  fof(c_0_88, plain, ![X15]:((v1_relat_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(v1_funct_1(k2_funct_1(X15))|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.47  cnf(c_0_89, plain, (v2_funct_1(X1)|~v2_funct_1(k5_relat_1(X1,X2))|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.19/0.47  cnf(c_0_90, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relset_1(esk1_0,esk1_0,esk3_0),k2_relset_1(esk1_0,esk1_0,esk3_0))))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84, c_0_81]), c_0_29]), c_0_68])]), c_0_67])).
% 0.19/0.47  cnf(c_0_91, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.47  cnf(c_0_92, plain, (k2_relat_1(X1)=k2_relat_1(X2)|~v5_relat_1(X1,k2_relat_1(X2))|~v5_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(pm,[status(thm)],[c_0_66, c_0_54])).
% 0.19/0.47  cnf(c_0_93, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0), inference(rw,[status(thm)],[c_0_67, c_0_85])).
% 0.19/0.47  cnf(c_0_94, negated_conjecture, (v5_relat_1(k2_funct_1(esk3_0),esk1_0)|~v2_funct_1(esk3_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_86, c_0_87]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_95, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.47  cnf(c_0_96, negated_conjecture, (v2_funct_1(esk3_0)|k2_relset_1(esk1_0,esk1_0,esk3_0)!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_89, c_0_70]), c_0_58]), c_0_44]), c_0_45]), c_0_67]), c_0_34]), c_0_29]), c_0_59]), c_0_68])])).
% 0.19/0.47  fof(c_0_97, plain, ![X52, X53, X54]:(((v1_funct_1(k2_funct_1(X54))|(~v2_funct_1(X54)|k2_relset_1(X52,X53,X54)!=X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&(v1_funct_2(k2_funct_1(X54),X53,X52)|(~v2_funct_1(X54)|k2_relset_1(X52,X53,X54)!=X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53))))))&(m1_subset_1(k2_funct_1(X54),k1_zfmisc_1(k2_zfmisc_1(X53,X52)))|(~v2_funct_1(X54)|k2_relset_1(X52,X53,X54)!=X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X53)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.47  cnf(c_0_98, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relset_1(esk1_0,esk1_0,esk3_0))))), inference(rw,[status(thm)],[c_0_90, c_0_82])).
% 0.19/0.47  cnf(c_0_99, negated_conjecture, (v1_funct_2(esk3_0,k1_relset_1(esk1_0,esk1_0,esk3_0),k2_relset_1(esk1_0,esk1_0,esk3_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91, c_0_81]), c_0_29]), c_0_68])]), c_0_67])).
% 0.19/0.47  cnf(c_0_100, negated_conjecture, (k2_relat_1(X1)=esk1_0|~v5_relat_1(esk3_0,k2_relat_1(X1))|~v5_relat_1(X1,esk1_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92, c_0_93]), c_0_67]), c_0_85]), c_0_68])])).
% 0.19/0.47  cnf(c_0_101, negated_conjecture, (v5_relat_1(k2_funct_1(esk3_0),esk1_0)|~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_94, c_0_95]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_102, negated_conjecture, (v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_85])])).
% 0.19/0.47  cnf(c_0_103, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.47  cnf(c_0_104, negated_conjecture, (k2_relset_1(esk1_0,k2_relset_1(esk1_0,esk1_0,esk3_0),esk3_0)=k2_relset_1(esk1_0,esk1_0,esk3_0)), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46, c_0_98]), c_0_67])).
% 0.19/0.47  cnf(c_0_105, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,k2_relset_1(esk1_0,esk1_0,esk3_0))), inference(rw,[status(thm)],[c_0_99, c_0_82])).
% 0.19/0.47  cnf(c_0_106, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.47  cnf(c_0_107, negated_conjecture, (k2_relat_1(k2_funct_1(X1))=esk1_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v5_relat_1(esk3_0,k1_relat_1(X1))|~v5_relat_1(k2_funct_1(X1),esk1_0)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_100, c_0_80])).
% 0.19/0.47  cnf(c_0_108, negated_conjecture, (v5_relat_1(k2_funct_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_101, c_0_102])])).
% 0.19/0.47  cnf(c_0_109, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))|~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103, c_0_98]), c_0_29])]), c_0_104]), c_0_105])])).
% 0.19/0.47  cnf(c_0_110, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.47  cnf(c_0_111, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_84, c_0_106])).
% 0.19/0.47  cnf(c_0_112, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))=esk1_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107, c_0_87]), c_0_78]), c_0_102]), c_0_29]), c_0_108]), c_0_68])])).
% 0.19/0.47  cnf(c_0_113, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_102])])).
% 0.19/0.47  cnf(c_0_114, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),k2_relset_1(esk1_0,esk1_0,esk3_0),esk1_0)|~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_110, c_0_98]), c_0_104]), c_0_105]), c_0_29])])).
% 0.19/0.47  cnf(c_0_115, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_111, c_0_112]), c_0_67]), c_0_85]), c_0_102]), c_0_113]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_116, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),esk1_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_85]), c_0_102])])).
% 0.19/0.47  fof(c_0_117, plain, ![X16, X17]:(~v1_relat_1(X16)|~v1_funct_1(X16)|(~v1_relat_1(X17)|~v1_funct_1(X17)|(k2_relat_1(X16)!=k1_relat_1(X17)|k5_relat_1(X16,X17)!=X16|X17=k6_relat_1(k1_relat_1(X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).
% 0.19/0.47  fof(c_0_118, plain, ![X23]:((k5_relat_1(X23,k2_funct_1(X23))=k6_relat_1(k1_relat_1(X23))|~v2_funct_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(k5_relat_1(k2_funct_1(X23),X23)=k6_relat_1(k2_relat_1(X23))|~v2_funct_1(X23)|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.19/0.47  cnf(c_0_119, negated_conjecture, (k1_relset_1(esk1_0,esk1_0,k2_funct_1(esk3_0))=esk1_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32, c_0_115]), c_0_116]), c_0_113])])).
% 0.19/0.47  cnf(c_0_120, plain, (X2=k6_relat_1(k1_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.19/0.47  cnf(c_0_121, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.19/0.47  cnf(c_0_122, negated_conjecture, (k1_relset_1(esk1_0,esk1_0,k2_funct_1(esk3_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_119, c_0_95]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_123, plain, (k6_relat_1(k1_relat_1(k2_funct_1(X1)))=k2_funct_1(X1)|k1_relat_1(k2_funct_1(X1))!=k2_relat_1(X1)|k6_relat_1(k1_relat_1(X1))!=X1|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_120, c_0_121])).
% 0.19/0.47  cnf(c_0_124, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))=esk1_0|~v1_relat_1(k2_funct_1(esk3_0))), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30, c_0_115]), c_0_122])).
% 0.19/0.47  cnf(c_0_125, negated_conjecture, (k2_funct_1(esk3_0)=k6_relat_1(esk1_0)|k1_relat_1(k2_funct_1(esk3_0))!=esk1_0|esk3_0!=k6_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_123, c_0_124]), c_0_67]), c_0_85]), c_0_81]), c_0_82]), c_0_102]), c_0_113]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_126, negated_conjecture, (k2_funct_1(esk3_0)=k6_relat_1(esk1_0)|esk3_0!=k6_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125, c_0_106]), c_0_67]), c_0_85]), c_0_102]), c_0_29]), c_0_68])])).
% 0.19/0.47  fof(c_0_127, plain, ![X51]:k6_partfun1(X51)=k6_relat_1(X51), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.47  cnf(c_0_128, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.47  cnf(c_0_129, negated_conjecture, (k2_funct_1(esk3_0)=k6_relat_1(esk1_0)|esk3_0!=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_126, c_0_95]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_130, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.47  cnf(c_0_131, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_127])).
% 0.19/0.47  cnf(c_0_132, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,esk3_0,X1)|esk3_0!=X1|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(pm,[status(thm)],[c_0_128, c_0_28])).
% 0.19/0.47  cnf(c_0_133, negated_conjecture, (m1_subset_1(k6_relat_1(esk1_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))|esk3_0!=k6_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_115, c_0_129])).
% 0.19/0.47  cnf(c_0_134, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_130, c_0_131])).
% 0.19/0.47  cnf(c_0_135, negated_conjecture, (esk3_0!=k6_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_132, c_0_133]), c_0_134])).
% 0.19/0.47  cnf(c_0_136, plain, (k6_relat_1(k1_relat_1(X1))=X1|k5_relat_1(k2_funct_1(X2),X1)!=k2_funct_1(X2)|k1_relat_1(X2)!=k1_relat_1(X1)|~v2_funct_1(X2)|~v1_funct_1(k2_funct_1(X2))|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(k2_funct_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(pm,[status(thm)],[c_0_120, c_0_80])).
% 0.19/0.47  cnf(c_0_137, negated_conjecture, (esk3_0!=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_135, c_0_95]), c_0_29]), c_0_68])])).
% 0.19/0.47  fof(c_0_138, plain, ![X24, X25]:(~v1_relat_1(X24)|~v1_funct_1(X24)|(~v1_relat_1(X25)|~v1_funct_1(X25)|(~v2_funct_1(X24)|~v2_funct_1(X25)|k2_funct_1(k5_relat_1(X24,X25))=k5_relat_1(k2_funct_1(X25),k2_funct_1(X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).
% 0.19/0.47  cnf(c_0_139, negated_conjecture, (k5_relat_1(k2_funct_1(X1),esk3_0)!=k2_funct_1(X1)|k1_relat_1(X1)!=esk1_0|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_136, c_0_87]), c_0_81]), c_0_82]), c_0_29]), c_0_68])]), c_0_137])).
% 0.19/0.47  cnf(c_0_140, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_118])).
% 0.19/0.47  cnf(c_0_141, plain, (k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_138])).
% 0.19/0.47  cnf(c_0_142, negated_conjecture, (k2_funct_1(esk3_0)!=k6_relat_1(esk1_0)|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_139, c_0_140]), c_0_67]), c_0_85]), c_0_81]), c_0_82]), c_0_102]), c_0_113]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_143, negated_conjecture, (v1_funct_2(esk2_0,k1_relset_1(esk1_0,esk1_0,esk2_0),k2_relset_1(esk1_0,esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_91, c_0_44]), c_0_34]), c_0_59])]), c_0_57])).
% 0.19/0.47  cnf(c_0_144, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relset_1(esk1_0,esk1_0,esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84, c_0_56]), c_0_57]), c_0_34]), c_0_59])])).
% 0.19/0.47  cnf(c_0_145, plain, (k6_relat_1(k1_relat_1(k2_funct_1(X1)))=k2_funct_1(X1)|k1_relat_1(k2_funct_1(X1))!=k2_relat_1(k2_funct_1(X2))|k2_funct_1(k5_relat_1(X1,X2))!=k2_funct_1(X2)|~v2_funct_1(X2)|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(k2_funct_1(X2))|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(k2_funct_1(X2))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_120, c_0_141])).
% 0.19/0.47  cnf(c_0_146, negated_conjecture, (k2_funct_1(esk3_0)!=k6_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_142, c_0_95]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_147, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,k2_relset_1(esk1_0,esk1_0,esk2_0))), inference(rw,[status(thm)],[c_0_143, c_0_45])).
% 0.19/0.47  cnf(c_0_148, negated_conjecture, (k2_relset_1(esk1_0,k2_relset_1(esk1_0,esk1_0,esk2_0),esk2_0)=k2_relset_1(esk1_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46, c_0_144]), c_0_57])).
% 0.19/0.47  cnf(c_0_149, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))!=k2_relat_1(k2_funct_1(X1))|k2_funct_1(k5_relat_1(esk3_0,X1))!=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_145, c_0_124]), c_0_102]), c_0_113]), c_0_29]), c_0_68])]), c_0_146])).
% 0.19/0.47  cnf(c_0_150, negated_conjecture, (v1_funct_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_103, c_0_144]), c_0_147]), c_0_58]), c_0_34])]), c_0_148])])).
% 0.19/0.47  cnf(c_0_151, negated_conjecture, (k2_relat_1(k2_funct_1(esk2_0))!=k1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_149, c_0_70]), c_0_58]), c_0_150]), c_0_34]), c_0_59])])).
% 0.19/0.47  cnf(c_0_152, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))!=esk1_0|~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_151, c_0_80]), c_0_44]), c_0_45]), c_0_58]), c_0_34]), c_0_59])])).
% 0.19/0.47  cnf(c_0_153, negated_conjecture, (~v1_relat_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_152, c_0_106]), c_0_67]), c_0_85]), c_0_102]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_154, negated_conjecture, (~v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_153, c_0_95]), c_0_29]), c_0_68])])).
% 0.19/0.47  cnf(c_0_155, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_154, c_0_95]), c_0_34]), c_0_59])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 156
% 0.19/0.47  # Proof object clause steps            : 111
% 0.19/0.47  # Proof object formula steps           : 45
% 0.19/0.47  # Proof object conjectures             : 77
% 0.19/0.47  # Proof object clause conjectures      : 74
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 37
% 0.19/0.47  # Proof object initial formulas used   : 22
% 0.19/0.47  # Proof object generating inferences   : 62
% 0.19/0.47  # Proof object simplifying inferences  : 194
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 22
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 44
% 0.19/0.47  # Removed in clause preprocessing      : 2
% 0.19/0.47  # Initial clauses in saturation        : 42
% 0.19/0.47  # Processed clauses                    : 678
% 0.19/0.47  # ...of these trivial                  : 31
% 0.19/0.47  # ...subsumed                          : 127
% 0.19/0.47  # ...remaining for further processing  : 520
% 0.19/0.47  # Other redundant clauses eliminated   : 0
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 36
% 0.19/0.47  # Backward-rewritten                   : 52
% 0.19/0.47  # Generated clauses                    : 2691
% 0.19/0.47  # ...of the previous two non-trivial   : 2448
% 0.19/0.47  # Contextual simplify-reflections      : 0
% 0.19/0.47  # Paramodulations                      : 2684
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 7
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 432
% 0.19/0.47  #    Positive orientable unit clauses  : 206
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 4
% 0.19/0.47  #    Non-unit-clauses                  : 222
% 0.19/0.47  # Current number of unprocessed clauses: 1749
% 0.19/0.47  # ...number of literals in the above   : 7399
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 89
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 1677
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 1114
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 139
% 0.19/0.47  # Unit Clause-clause subsumption calls : 336
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 405
% 0.19/0.47  # BW rewrite match successes           : 11
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 39265
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.124 s
% 0.19/0.47  # System time              : 0.008 s
% 0.19/0.47  # Total time               : 0.133 s
% 0.19/0.47  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
