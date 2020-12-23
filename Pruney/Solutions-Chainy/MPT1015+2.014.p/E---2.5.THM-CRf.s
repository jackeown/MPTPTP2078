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
% DateTime   : Thu Dec  3 11:05:47 EST 2020

% Result     : Theorem 0.62s
% Output     : CNFRefutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  149 (6287 expanded)
%              Number of clauses        :   93 (2349 expanded)
%              Number of leaves         :   28 (1636 expanded)
%              Depth                    :   20
%              Number of atoms          :  482 (28352 expanded)
%              Number of equality atoms :  102 (1452 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

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

fof(t177_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v2_funct_1(X1)
            & r1_tarski(X2,k1_relat_1(X1)) )
         => k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(t160_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t26_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X2,X3)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))
           => ( ( X3 = k1_xboole_0
                & X2 != k1_xboole_0 )
              | v2_funct_1(X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(c_0_28,negated_conjecture,(
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

fof(c_0_29,plain,(
    ! [X36,X37,X38] :
      ( ( v4_relat_1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v5_relat_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_30,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)
    & v2_funct_1(esk2_0)
    & ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).

fof(c_0_31,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_32,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_33,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v4_relat_1(X22,X21)
      | X22 = k7_relat_1(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_34,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_38,plain,(
    ! [X81] :
      ( ( v1_funct_1(X81)
        | ~ v1_relat_1(X81)
        | ~ v1_funct_1(X81) )
      & ( v1_funct_2(X81,k1_relat_1(X81),k2_relat_1(X81))
        | ~ v1_relat_1(X81)
        | ~ v1_funct_1(X81) )
      & ( m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X81),k2_relat_1(X81))))
        | ~ v1_relat_1(X81)
        | ~ v1_funct_1(X81) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_39,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k2_relat_1(k7_relat_1(X18,X17)) = k9_relat_1(X18,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_40,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v4_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_37])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k7_relat_1(esk2_0,esk1_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

fof(c_0_46,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k1_relset_1(X42,X43,X44) = k1_relat_1(X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_47,plain,(
    ! [X82,X83] :
      ( ~ v1_funct_1(X83)
      | ~ v1_funct_2(X83,X82,X82)
      | ~ m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X82,X82)))
      | k1_relset_1(X82,X82,X83) = X82 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(X1,X2)),k9_relat_1(X1,X2))))
    | ~ v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k9_relat_1(esk2_0,esk1_0) = k2_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_42])])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_51,plain,(
    ! [X31] :
      ( ( k2_relat_1(X31) = k1_relat_1(k2_funct_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( k1_relat_1(X31) = k2_relat_1(k2_funct_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_52,plain,(
    ! [X24] :
      ( ( v1_relat_1(k2_funct_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( v1_funct_1(k2_funct_1(X24))
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_53,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_55,plain,(
    ! [X52,X53,X54,X55] :
      ( ( ~ r2_relset_1(X52,X53,X54,X55)
        | X54 = X55
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) )
      & ( X54 != X55
        | r2_relset_1(X52,X53,X54,X55)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_45]),c_0_45]),c_0_45]),c_0_50]),c_0_45]),c_0_42]),c_0_42])])).

cnf(c_0_57,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_62,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_64,plain,(
    ! [X59,X60,X61,X62,X63,X64] :
      ( ( v1_funct_1(k1_partfun1(X59,X60,X61,X62,X63,X64))
        | ~ v1_funct_1(X63)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(X64)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( m1_subset_1(k1_partfun1(X59,X60,X61,X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(X59,X62)))
        | ~ v1_funct_1(X63)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
        | ~ v1_funct_1(X64)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_65,negated_conjecture,
    ( v4_relat_1(esk2_0,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_56])).

fof(c_0_66,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_67,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_57]),c_0_58]),c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_50]),c_0_35])])).

cnf(c_0_69,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_70,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ v1_funct_1(X27)
      | ~ v2_funct_1(X27)
      | ~ r1_tarski(X28,k1_relat_1(X27))
      | k9_relat_1(k2_funct_1(X27),k9_relat_1(X27,X28)) = X28 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t177_funct_1])])])).

fof(c_0_71,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | k2_relat_1(k5_relat_1(X19,X20)) = k9_relat_1(X20,k2_relat_1(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).

fof(c_0_72,plain,(
    ! [X66,X67,X68,X69,X70,X71] :
      ( ~ v1_funct_1(X70)
      | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
      | ~ v1_funct_1(X71)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
      | k1_partfun1(X66,X67,X68,X69,X70,X71) = k5_relat_1(X70,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_73,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) = esk2_0
    | ~ m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_35])])).

cnf(c_0_74,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_77,negated_conjecture,
    ( k7_relat_1(esk2_0,k1_relat_1(esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_65]),c_0_42])])).

cnf(c_0_78,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk2_0)),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_50]),c_0_42])])).

cnf(c_0_80,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_81,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | k2_relat_1(X29) != k1_relat_1(X30)
      | k5_relat_1(X29,X30) != X29
      | X30 = k6_relat_1(k1_relat_1(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).

cnf(c_0_82,plain,
    ( k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_83,plain,
    ( k2_relat_1(k5_relat_1(X1,X2)) = k9_relat_1(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_84,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_85,negated_conjecture,
    ( k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_50]),c_0_75]),c_0_35]),c_0_76])])).

cnf(c_0_86,negated_conjecture,
    ( k9_relat_1(esk2_0,k1_relat_1(esk2_0)) = k2_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_77]),c_0_42])])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_69]),c_0_50]),c_0_42])])).

fof(c_0_89,plain,(
    ! [X32] :
      ( ( k5_relat_1(X32,k2_funct_1(X32)) = k6_relat_1(k1_relat_1(X32))
        | ~ v2_funct_1(X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( k5_relat_1(k2_funct_1(X32),X32) = k6_relat_1(k2_relat_1(X32))
        | ~ v2_funct_1(X32)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_90,plain,
    ( X2 = k6_relat_1(k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

fof(c_0_91,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ v2_funct_1(X33)
      | ~ v2_funct_1(X34)
      | k2_funct_1(k5_relat_1(X33,X34)) = k5_relat_1(k2_funct_1(X34),k2_funct_1(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).

cnf(c_0_92,plain,
    ( k9_relat_1(k2_funct_1(X1),k2_relat_1(k5_relat_1(X2,X1))) = k2_relat_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( k5_relat_1(esk3_0,esk2_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_50]),c_0_75]),c_0_35]),c_0_76])])).

cnf(c_0_94,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk2_0),k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_86]),c_0_69]),c_0_50]),c_0_42]),c_0_87])])).

cnf(c_0_95,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_76]),c_0_37])])).

fof(c_0_96,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_97,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_98,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk2_0),k2_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_79]),c_0_37])])).

cnf(c_0_100,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_101,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_102,plain,(
    ! [X72] : k6_partfun1(X72) = k6_relat_1(X72) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_103,plain,
    ( k6_relat_1(k2_relat_1(X1)) = k2_funct_1(X1)
    | k5_relat_1(X2,k2_funct_1(X1)) != X2
    | k2_relat_1(X1) != k2_relat_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_80]),c_0_58]),c_0_59])).

cnf(c_0_104,plain,
    ( k2_funct_1(k5_relat_1(X1,X2)) = k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_105,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0
    | ~ r1_tarski(k2_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_68]),c_0_69]),c_0_50]),c_0_42]),c_0_95]),c_0_68])])).

cnf(c_0_106,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_107,negated_conjecture,
    ( v5_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_76])).

cnf(c_0_108,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk2_0),k2_relat_1(esk2_0)) = k2_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_98]),c_0_99])])).

cnf(c_0_109,plain,
    ( k6_relat_1(k1_relat_1(X1)) = X1
    | k6_relat_1(k2_relat_1(X1)) != k2_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_100]),c_0_58]),c_0_59]),c_0_57])).

cnf(c_0_110,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_101]),c_0_75]),c_0_76])])).

cnf(c_0_111,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_112,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_113,plain,
    ( k6_relat_1(k2_relat_1(X1)) = k2_funct_1(X1)
    | k2_funct_1(k5_relat_1(X1,X2)) != k2_funct_1(X2)
    | k2_relat_1(X1) != k2_relat_1(k2_funct_1(X2))
    | ~ v2_funct_1(X1)
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_58]),c_0_59])).

cnf(c_0_114,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_107]),c_0_95])])).

cnf(c_0_115,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk2_0)) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_108]),c_0_94]),c_0_68]),c_0_99])])).

cnf(c_0_116,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk3_0
    | k6_relat_1(k2_relat_1(esk3_0)) != k2_funct_1(esk3_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_75]),c_0_95])])).

fof(c_0_117,plain,(
    ! [X65] :
      ( v1_partfun1(k6_partfun1(X65),X65)
      & m1_subset_1(k6_partfun1(X65),k1_zfmisc_1(k2_zfmisc_1(X65,X65))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

cnf(c_0_118,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_119,negated_conjecture,
    ( k6_relat_1(esk1_0) = k2_funct_1(esk3_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_93]),c_0_114]),c_0_114]),c_0_115]),c_0_69]),c_0_75]),c_0_50]),c_0_95]),c_0_42])])).

cnf(c_0_120,negated_conjecture,
    ( k6_relat_1(esk1_0) = esk3_0
    | k6_relat_1(esk1_0) != k2_funct_1(esk3_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_116,c_0_114])).

fof(c_0_121,plain,(
    ! [X9,X10] :
      ( ~ v1_xboole_0(X9)
      | X9 = X10
      | ~ v1_xboole_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_122,plain,(
    ! [X39,X40,X41] :
      ( ~ v1_xboole_0(X39)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X39)))
      | v1_xboole_0(X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_123,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

fof(c_0_124,plain,(
    ! [X73,X74,X75,X76,X77] :
      ( ( X75 = k1_xboole_0
        | v2_funct_1(X76)
        | ~ v2_funct_1(k1_partfun1(X73,X74,X74,X75,X76,X77))
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X74,X75)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X73,X74)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( X74 != k1_xboole_0
        | v2_funct_1(X76)
        | ~ v2_funct_1(k1_partfun1(X73,X74,X74,X75,X76,X77))
        | ~ v1_funct_1(X77)
        | ~ v1_funct_2(X77,X74,X75)
        | ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X74,X75)))
        | ~ v1_funct_1(X76)
        | ~ v1_funct_2(X76,X73,X74)
        | ~ m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).

cnf(c_0_125,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_1(esk3_0))
    | ~ v2_funct_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_126,negated_conjecture,
    ( k2_funct_1(esk3_0) = esk3_0
    | ~ v2_funct_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_119])).

cnf(c_0_127,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_128,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_121])).

cnf(c_0_129,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_130,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_122])).

cnf(c_0_131,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_123,c_0_112])).

cnf(c_0_132,plain,
    ( X1 = k1_xboole_0
    | v2_funct_1(X2)
    | ~ v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_133,negated_conjecture,
    ( ~ r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0)
    | ~ v2_funct_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_134,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_127])).

cnf(c_0_135,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_136,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_130,c_0_131])).

cnf(c_0_137,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_130,c_0_76])).

cnf(c_0_138,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_85]),c_0_61]),c_0_101]),c_0_69]),c_0_50]),c_0_75]),c_0_35]),c_0_76])])).

cnf(c_0_139,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_76])])).

fof(c_0_140,plain,(
    ! [X26] :
      ( v1_relat_1(k6_relat_1(X26))
      & v2_funct_1(k6_relat_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_141,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_142,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_137])).

cnf(c_0_143,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_144,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

cnf(c_0_145,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_141,c_0_129])).

cnf(c_0_146,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_143]),c_0_129])])).

cnf(c_0_147,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_144,c_0_145])).

cnf(c_0_148,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139,c_0_146]),c_0_147])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.62/0.85  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.62/0.85  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.62/0.85  #
% 0.62/0.85  # Preprocessing time       : 0.029 s
% 0.62/0.85  # Presaturation interreduction done
% 0.62/0.85  
% 0.62/0.85  # Proof found!
% 0.62/0.85  # SZS status Theorem
% 0.62/0.85  # SZS output start CNFRefutation
% 0.62/0.85  fof(t76_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 0.62/0.85  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.62/0.85  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.62/0.85  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.62/0.85  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.62/0.85  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.62/0.85  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.62/0.85  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.62/0.85  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.62/0.85  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.62/0.85  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.62/0.85  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.62/0.85  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.62/0.85  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.62/0.85  fof(t177_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v2_funct_1(X1)&r1_tarski(X2,k1_relat_1(X1)))=>k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 0.62/0.85  fof(t160_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 0.62/0.85  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.62/0.85  fof(t44_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k2_relat_1(X1)=k1_relat_1(X2)&k5_relat_1(X1,X2)=X1)=>X2=k6_relat_1(k1_relat_1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 0.62/0.85  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 0.62/0.85  fof(t66_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X1)&v2_funct_1(X2))=>k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 0.62/0.85  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.62/0.85  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.62/0.85  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.62/0.85  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.62/0.85  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.62/0.85  fof(t26_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v2_funct_1(k1_partfun1(X1,X2,X2,X3,X4,X5))=>((X3=k1_xboole_0&X2!=k1_xboole_0)|v2_funct_1(X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 0.62/0.85  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.62/0.85  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.62/0.85  fof(c_0_28, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X1))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X3,X2),X2)&v2_funct_1(X2))=>r2_relset_1(X1,X1,X3,k6_partfun1(X1)))))), inference(assume_negation,[status(cth)],[t76_funct_2])).
% 0.62/0.85  fof(c_0_29, plain, ![X36, X37, X38]:((v4_relat_1(X38,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(v5_relat_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.62/0.85  fof(c_0_30, negated_conjecture, (((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk1_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)&v2_funct_1(esk2_0))&~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_28])])])).
% 0.62/0.85  fof(c_0_31, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.62/0.85  fof(c_0_32, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.62/0.85  fof(c_0_33, plain, ![X21, X22]:(~v1_relat_1(X22)|~v4_relat_1(X22,X21)|X22=k7_relat_1(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.62/0.85  cnf(c_0_34, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.85  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  cnf(c_0_36, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.62/0.85  cnf(c_0_37, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.62/0.85  fof(c_0_38, plain, ![X81]:(((v1_funct_1(X81)|(~v1_relat_1(X81)|~v1_funct_1(X81)))&(v1_funct_2(X81,k1_relat_1(X81),k2_relat_1(X81))|(~v1_relat_1(X81)|~v1_funct_1(X81))))&(m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X81),k2_relat_1(X81))))|(~v1_relat_1(X81)|~v1_funct_1(X81)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.62/0.85  fof(c_0_39, plain, ![X17, X18]:(~v1_relat_1(X18)|k2_relat_1(k7_relat_1(X18,X17))=k9_relat_1(X18,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.62/0.85  cnf(c_0_40, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.62/0.85  cnf(c_0_41, negated_conjecture, (v4_relat_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.62/0.85  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_37])])).
% 0.62/0.85  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.62/0.85  cnf(c_0_44, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.62/0.85  cnf(c_0_45, negated_conjecture, (k7_relat_1(esk2_0,esk1_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.62/0.85  fof(c_0_46, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k1_relset_1(X42,X43,X44)=k1_relat_1(X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.62/0.85  fof(c_0_47, plain, ![X82, X83]:(~v1_funct_1(X83)|~v1_funct_2(X83,X82,X82)|~m1_subset_1(X83,k1_zfmisc_1(k2_zfmisc_1(X82,X82)))|k1_relset_1(X82,X82,X83)=X82), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.62/0.85  cnf(c_0_48, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(X1,X2)),k9_relat_1(X1,X2))))|~v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.62/0.85  cnf(c_0_49, negated_conjecture, (k9_relat_1(esk2_0,esk1_0)=k2_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_42])])).
% 0.62/0.85  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  fof(c_0_51, plain, ![X31]:((k2_relat_1(X31)=k1_relat_1(k2_funct_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(k1_relat_1(X31)=k2_relat_1(k2_funct_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.62/0.85  fof(c_0_52, plain, ![X24]:((v1_relat_1(k2_funct_1(X24))|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(v1_funct_1(k2_funct_1(X24))|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.62/0.85  cnf(c_0_53, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.62/0.85  cnf(c_0_54, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.62/0.85  fof(c_0_55, plain, ![X52, X53, X54, X55]:((~r2_relset_1(X52,X53,X54,X55)|X54=X55|(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))&(X54!=X55|r2_relset_1(X52,X53,X54,X55)|(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.62/0.85  cnf(c_0_56, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_45]), c_0_45]), c_0_45]), c_0_50]), c_0_45]), c_0_42]), c_0_42])])).
% 0.62/0.85  cnf(c_0_57, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.62/0.85  cnf(c_0_58, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.62/0.85  cnf(c_0_59, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.62/0.85  cnf(c_0_60, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.62/0.85  cnf(c_0_61, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  cnf(c_0_62, plain, (X3=X4|~r2_relset_1(X1,X2,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.62/0.85  cnf(c_0_63, negated_conjecture, (r2_relset_1(esk1_0,esk1_0,k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  fof(c_0_64, plain, ![X59, X60, X61, X62, X63, X64]:((v1_funct_1(k1_partfun1(X59,X60,X61,X62,X63,X64))|(~v1_funct_1(X63)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|~v1_funct_1(X64)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))))&(m1_subset_1(k1_partfun1(X59,X60,X61,X62,X63,X64),k1_zfmisc_1(k2_zfmisc_1(X59,X62)))|(~v1_funct_1(X63)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|~v1_funct_1(X64)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.62/0.85  cnf(c_0_65, negated_conjecture, (v4_relat_1(esk2_0,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_56])).
% 0.62/0.85  fof(c_0_66, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.62/0.85  cnf(c_0_67, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_57]), c_0_58]), c_0_59])).
% 0.62/0.85  cnf(c_0_68, negated_conjecture, (k1_relat_1(esk2_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_50]), c_0_35])])).
% 0.62/0.85  cnf(c_0_69, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  fof(c_0_70, plain, ![X27, X28]:(~v1_relat_1(X27)|~v1_funct_1(X27)|(~v2_funct_1(X27)|~r1_tarski(X28,k1_relat_1(X27))|k9_relat_1(k2_funct_1(X27),k9_relat_1(X27,X28))=X28)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t177_funct_1])])])).
% 0.62/0.85  fof(c_0_71, plain, ![X19, X20]:(~v1_relat_1(X19)|(~v1_relat_1(X20)|k2_relat_1(k5_relat_1(X19,X20))=k9_relat_1(X20,k2_relat_1(X19)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t160_relat_1])])])).
% 0.62/0.85  fof(c_0_72, plain, ![X66, X67, X68, X69, X70, X71]:(~v1_funct_1(X70)|~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))|~v1_funct_1(X71)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))|k1_partfun1(X66,X67,X68,X69,X70,X71)=k5_relat_1(X70,X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.62/0.85  cnf(c_0_73, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)=esk2_0|~m1_subset_1(k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_35])])).
% 0.62/0.85  cnf(c_0_74, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.62/0.85  cnf(c_0_75, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  cnf(c_0_77, negated_conjecture, (k7_relat_1(esk2_0,k1_relat_1(esk2_0))=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_65]), c_0_42])])).
% 0.62/0.85  cnf(c_0_78, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.62/0.85  cnf(c_0_79, negated_conjecture, (m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk2_0)),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_50]), c_0_42])])).
% 0.62/0.85  cnf(c_0_80, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.62/0.85  fof(c_0_81, plain, ![X29, X30]:(~v1_relat_1(X29)|~v1_funct_1(X29)|(~v1_relat_1(X30)|~v1_funct_1(X30)|(k2_relat_1(X29)!=k1_relat_1(X30)|k5_relat_1(X29,X30)!=X29|X30=k6_relat_1(k1_relat_1(X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_1])])])).
% 0.62/0.85  cnf(c_0_82, plain, (k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.62/0.85  cnf(c_0_83, plain, (k2_relat_1(k5_relat_1(X1,X2))=k9_relat_1(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.62/0.85  cnf(c_0_84, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.62/0.85  cnf(c_0_85, negated_conjecture, (k1_partfun1(esk1_0,esk1_0,esk1_0,esk1_0,esk3_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_50]), c_0_75]), c_0_35]), c_0_76])])).
% 0.62/0.85  cnf(c_0_86, negated_conjecture, (k9_relat_1(esk2_0,k1_relat_1(esk2_0))=k2_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_77]), c_0_42])])).
% 0.62/0.85  cnf(c_0_87, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_78])).
% 0.62/0.85  cnf(c_0_88, negated_conjecture, (m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_69]), c_0_50]), c_0_42])])).
% 0.62/0.85  fof(c_0_89, plain, ![X32]:((k5_relat_1(X32,k2_funct_1(X32))=k6_relat_1(k1_relat_1(X32))|~v2_funct_1(X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(k5_relat_1(k2_funct_1(X32),X32)=k6_relat_1(k2_relat_1(X32))|~v2_funct_1(X32)|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.62/0.85  cnf(c_0_90, plain, (X2=k6_relat_1(k1_relat_1(X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.62/0.85  fof(c_0_91, plain, ![X33, X34]:(~v1_relat_1(X33)|~v1_funct_1(X33)|(~v1_relat_1(X34)|~v1_funct_1(X34)|(~v2_funct_1(X33)|~v2_funct_1(X34)|k2_funct_1(k5_relat_1(X33,X34))=k5_relat_1(k2_funct_1(X34),k2_funct_1(X33))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_1])])])).
% 0.62/0.85  cnf(c_0_92, plain, (k9_relat_1(k2_funct_1(X1),k2_relat_1(k5_relat_1(X2,X1)))=k2_relat_1(X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.62/0.85  cnf(c_0_93, negated_conjecture, (k5_relat_1(esk3_0,esk2_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_50]), c_0_75]), c_0_35]), c_0_76])])).
% 0.62/0.85  cnf(c_0_94, negated_conjecture, (k9_relat_1(k2_funct_1(esk2_0),k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_86]), c_0_69]), c_0_50]), c_0_42]), c_0_87])])).
% 0.62/0.85  cnf(c_0_95, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_76]), c_0_37])])).
% 0.62/0.85  fof(c_0_96, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.62/0.85  cnf(c_0_97, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.62/0.85  cnf(c_0_98, negated_conjecture, (v4_relat_1(k2_funct_1(esk2_0),k2_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_34, c_0_88])).
% 0.62/0.85  cnf(c_0_99, negated_conjecture, (v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_79]), c_0_37])])).
% 0.62/0.85  cnf(c_0_100, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.62/0.85  cnf(c_0_101, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  fof(c_0_102, plain, ![X72]:k6_partfun1(X72)=k6_relat_1(X72), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.62/0.85  cnf(c_0_103, plain, (k6_relat_1(k2_relat_1(X1))=k2_funct_1(X1)|k5_relat_1(X2,k2_funct_1(X1))!=X2|k2_relat_1(X1)!=k2_relat_1(X2)|~v2_funct_1(X1)|~v1_funct_1(X2)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_80]), c_0_58]), c_0_59])).
% 0.62/0.85  cnf(c_0_104, plain, (k2_funct_1(k5_relat_1(X1,X2))=k5_relat_1(k2_funct_1(X2),k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|~v2_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.62/0.85  cnf(c_0_105, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0|~r1_tarski(k2_relat_1(esk3_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_68]), c_0_69]), c_0_50]), c_0_42]), c_0_95]), c_0_68])])).
% 0.62/0.85  cnf(c_0_106, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.62/0.85  cnf(c_0_107, negated_conjecture, (v5_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_97, c_0_76])).
% 0.62/0.85  cnf(c_0_108, negated_conjecture, (k7_relat_1(k2_funct_1(esk2_0),k2_relat_1(esk2_0))=k2_funct_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_98]), c_0_99])])).
% 0.62/0.85  cnf(c_0_109, plain, (k6_relat_1(k1_relat_1(X1))=X1|k6_relat_1(k2_relat_1(X1))!=k2_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_100]), c_0_58]), c_0_59]), c_0_57])).
% 0.62/0.85  cnf(c_0_110, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_101]), c_0_75]), c_0_76])])).
% 0.62/0.85  cnf(c_0_111, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_partfun1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.62/0.85  cnf(c_0_112, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.62/0.85  cnf(c_0_113, plain, (k6_relat_1(k2_relat_1(X1))=k2_funct_1(X1)|k2_funct_1(k5_relat_1(X1,X2))!=k2_funct_1(X2)|k2_relat_1(X1)!=k2_relat_1(k2_funct_1(X2))|~v2_funct_1(X1)|~v2_funct_1(X2)|~v1_funct_1(X1)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_58]), c_0_59])).
% 0.62/0.85  cnf(c_0_114, negated_conjecture, (k2_relat_1(esk3_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_107]), c_0_95])])).
% 0.62/0.85  cnf(c_0_115, negated_conjecture, (k2_relat_1(k2_funct_1(esk2_0))=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_108]), c_0_94]), c_0_68]), c_0_99])])).
% 0.62/0.85  cnf(c_0_116, negated_conjecture, (k6_relat_1(esk1_0)=esk3_0|k6_relat_1(k2_relat_1(esk3_0))!=k2_funct_1(esk3_0)|~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_75]), c_0_95])])).
% 0.62/0.85  fof(c_0_117, plain, ![X65]:(v1_partfun1(k6_partfun1(X65),X65)&m1_subset_1(k6_partfun1(X65),k1_zfmisc_1(k2_zfmisc_1(X65,X65)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.62/0.85  cnf(c_0_118, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k6_relat_1(esk1_0))), inference(rw,[status(thm)],[c_0_111, c_0_112])).
% 0.62/0.85  cnf(c_0_119, negated_conjecture, (k6_relat_1(esk1_0)=k2_funct_1(esk3_0)|~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_93]), c_0_114]), c_0_114]), c_0_115]), c_0_69]), c_0_75]), c_0_50]), c_0_95]), c_0_42])])).
% 0.62/0.85  cnf(c_0_120, negated_conjecture, (k6_relat_1(esk1_0)=esk3_0|k6_relat_1(esk1_0)!=k2_funct_1(esk3_0)|~v2_funct_1(esk3_0)), inference(rw,[status(thm)],[c_0_116, c_0_114])).
% 0.62/0.85  fof(c_0_121, plain, ![X9, X10]:(~v1_xboole_0(X9)|X9=X10|~v1_xboole_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.62/0.85  fof(c_0_122, plain, ![X39, X40, X41]:(~v1_xboole_0(X39)|(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X40,X39)))|v1_xboole_0(X41))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.62/0.85  cnf(c_0_123, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.62/0.85  fof(c_0_124, plain, ![X73, X74, X75, X76, X77]:((X75=k1_xboole_0|v2_funct_1(X76)|~v2_funct_1(k1_partfun1(X73,X74,X74,X75,X76,X77))|(~v1_funct_1(X77)|~v1_funct_2(X77,X74,X75)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))|(~v1_funct_1(X76)|~v1_funct_2(X76,X73,X74)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))&(X74!=k1_xboole_0|v2_funct_1(X76)|~v2_funct_1(k1_partfun1(X73,X74,X74,X75,X76,X77))|(~v1_funct_1(X77)|~v1_funct_2(X77,X74,X75)|~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X74,X75))))|(~v1_funct_1(X76)|~v1_funct_2(X76,X73,X74)|~m1_subset_1(X76,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_funct_2])])])])).
% 0.62/0.85  cnf(c_0_125, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,k2_funct_1(esk3_0))|~v2_funct_1(esk3_0)), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.62/0.85  cnf(c_0_126, negated_conjecture, (k2_funct_1(esk3_0)=esk3_0|~v2_funct_1(esk3_0)), inference(spm,[status(thm)],[c_0_120, c_0_119])).
% 0.62/0.85  cnf(c_0_127, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.62/0.85  cnf(c_0_128, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_121])).
% 0.62/0.85  cnf(c_0_129, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.62/0.85  cnf(c_0_130, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_122])).
% 0.62/0.85  cnf(c_0_131, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_123, c_0_112])).
% 0.62/0.85  cnf(c_0_132, plain, (X1=k1_xboole_0|v2_funct_1(X2)|~v2_funct_1(k1_partfun1(X3,X4,X4,X1,X2,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_124])).
% 0.62/0.85  cnf(c_0_133, negated_conjecture, (~r2_relset_1(esk1_0,esk1_0,esk3_0,esk3_0)|~v2_funct_1(esk3_0)), inference(spm,[status(thm)],[c_0_125, c_0_126])).
% 0.62/0.85  cnf(c_0_134, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_127])).
% 0.62/0.85  cnf(c_0_135, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 0.62/0.85  cnf(c_0_136, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_130, c_0_131])).
% 0.62/0.85  cnf(c_0_137, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_130, c_0_76])).
% 0.62/0.85  cnf(c_0_138, negated_conjecture, (esk1_0=k1_xboole_0|v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_85]), c_0_61]), c_0_101]), c_0_69]), c_0_50]), c_0_75]), c_0_35]), c_0_76])])).
% 0.62/0.85  cnf(c_0_139, negated_conjecture, (~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_76])])).
% 0.62/0.85  fof(c_0_140, plain, ![X26]:(v1_relat_1(k6_relat_1(X26))&v2_funct_1(k6_relat_1(X26))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.62/0.85  cnf(c_0_141, plain, (k6_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 0.62/0.85  cnf(c_0_142, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_135, c_0_137])).
% 0.62/0.85  cnf(c_0_143, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_138, c_0_139])).
% 0.62/0.85  cnf(c_0_144, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_140])).
% 0.62/0.85  cnf(c_0_145, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_141, c_0_129])).
% 0.62/0.85  cnf(c_0_146, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_143]), c_0_129])])).
% 0.62/0.85  cnf(c_0_147, plain, (v2_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_144, c_0_145])).
% 0.62/0.85  cnf(c_0_148, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_139, c_0_146]), c_0_147])]), ['proof']).
% 0.62/0.85  # SZS output end CNFRefutation
% 0.62/0.85  # Proof object total steps             : 149
% 0.62/0.85  # Proof object clause steps            : 93
% 0.62/0.85  # Proof object formula steps           : 56
% 0.62/0.85  # Proof object conjectures             : 50
% 0.62/0.85  # Proof object clause conjectures      : 47
% 0.62/0.85  # Proof object formula conjectures     : 3
% 0.62/0.85  # Proof object initial clauses used    : 40
% 0.62/0.85  # Proof object initial formulas used   : 28
% 0.62/0.85  # Proof object generating inferences   : 45
% 0.62/0.85  # Proof object simplifying inferences  : 113
% 0.62/0.85  # Training examples: 0 positive, 0 negative
% 0.62/0.85  # Parsed axioms                        : 35
% 0.62/0.85  # Removed by relevancy pruning/SinE    : 0
% 0.62/0.85  # Initial clauses                      : 62
% 0.62/0.85  # Removed in clause preprocessing      : 2
% 0.62/0.85  # Initial clauses in saturation        : 60
% 0.62/0.85  # Processed clauses                    : 3439
% 0.62/0.85  # ...of these trivial                  : 71
% 0.62/0.85  # ...subsumed                          : 2097
% 0.62/0.85  # ...remaining for further processing  : 1271
% 0.62/0.85  # Other redundant clauses eliminated   : 19
% 0.62/0.85  # Clauses deleted for lack of memory   : 0
% 0.62/0.85  # Backward-subsumed                    : 51
% 0.62/0.85  # Backward-rewritten                   : 830
% 0.62/0.85  # Generated clauses                    : 15081
% 0.62/0.85  # ...of the previous two non-trivial   : 13571
% 0.62/0.85  # Contextual simplify-reflections      : 103
% 0.62/0.85  # Paramodulations                      : 15061
% 0.62/0.85  # Factorizations                       : 0
% 0.62/0.85  # Equation resolutions                 : 19
% 0.62/0.85  # Propositional unsat checks           : 0
% 0.62/0.85  #    Propositional check models        : 0
% 0.62/0.85  #    Propositional check unsatisfiable : 0
% 0.62/0.85  #    Propositional clauses             : 0
% 0.62/0.85  #    Propositional clauses after purity: 0
% 0.62/0.85  #    Propositional unsat core size     : 0
% 0.62/0.85  #    Propositional preprocessing time  : 0.000
% 0.62/0.85  #    Propositional encoding time       : 0.000
% 0.62/0.85  #    Propositional solver time         : 0.000
% 0.62/0.85  #    Success case prop preproc time    : 0.000
% 0.62/0.85  #    Success case prop encoding time   : 0.000
% 0.62/0.85  #    Success case prop solver time     : 0.000
% 0.62/0.85  # Current number of processed clauses  : 327
% 0.62/0.85  #    Positive orientable unit clauses  : 45
% 0.62/0.85  #    Positive unorientable unit clauses: 0
% 0.62/0.85  #    Negative unit clauses             : 0
% 0.62/0.85  #    Non-unit-clauses                  : 282
% 0.62/0.85  # Current number of unprocessed clauses: 10135
% 0.62/0.85  # ...number of literals in the above   : 55900
% 0.62/0.85  # Current number of archived formulas  : 0
% 0.62/0.85  # Current number of archived clauses   : 941
% 0.62/0.85  # Clause-clause subsumption calls (NU) : 172038
% 0.62/0.85  # Rec. Clause-clause subsumption calls : 73384
% 0.62/0.85  # Non-unit clause-clause subsumptions  : 2247
% 0.62/0.85  # Unit Clause-clause subsumption calls : 1282
% 0.62/0.85  # Rewrite failures with RHS unbound    : 0
% 0.62/0.85  # BW rewrite match attempts            : 24
% 0.62/0.85  # BW rewrite match successes           : 11
% 0.62/0.85  # Condensation attempts                : 0
% 0.62/0.85  # Condensation successes               : 0
% 0.62/0.85  # Termbank termtop insertions          : 342668
% 0.62/0.85  
% 0.62/0.85  # -------------------------------------------------
% 0.62/0.85  # User time                : 0.497 s
% 0.62/0.85  # System time              : 0.014 s
% 0.62/0.85  # Total time               : 0.511 s
% 0.62/0.85  # Maximum resident set size: 1624 pages
%------------------------------------------------------------------------------
