%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  173 (16910 expanded)
%              Number of clauses        :  111 (6227 expanded)
%              Number of leaves         :   31 (4324 expanded)
%              Depth                    :   27
%              Number of atoms          :  626 (83998 expanded)
%              Number of equality atoms :  157 (10483 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t177_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v2_funct_1(X1)
            & r1_tarski(X2,k1_relat_1(X1)) )
         => k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(cc6_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & ~ v1_xboole_0(X3)
              & v1_funct_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(reflexivity_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_funct_2(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_tops_2])).

fof(c_0_32,plain,(
    ! [X33,X34,X35] :
      ( ( v4_relat_1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v5_relat_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_33,negated_conjecture,
    ( l1_struct_0(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0)
    & v2_funct_1(esk4_0)
    & ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).

fof(c_0_34,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_35,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_36,plain,(
    ! [X45,X46] :
      ( ( ~ v1_partfun1(X46,X45)
        | k1_relat_1(X46) = X45
        | ~ v1_relat_1(X46)
        | ~ v4_relat_1(X46,X45) )
      & ( k1_relat_1(X46) != X45
        | v1_partfun1(X46,X45)
        | ~ v1_relat_1(X46)
        | ~ v4_relat_1(X46,X45) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_37,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_41,plain,(
    ! [X39,X40,X41] :
      ( ( v1_funct_1(X41)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | v1_xboole_0(X40) )
      & ( v1_partfun1(X41,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_42,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v4_relat_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_40])])).

cnf(c_0_45,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_48,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k2_relset_1(X36,X37,X38) = k2_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_49,plain,(
    ! [X66] :
      ( v2_struct_0(X66)
      | ~ l1_struct_0(X66)
      | ~ v1_xboole_0(u1_struct_0(X66)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk2_0)
    | ~ v1_partfun1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_51,negated_conjecture,
    ( v1_partfun1(esk4_0,u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_46]),c_0_47])])).

fof(c_0_52,plain,(
    ! [X65] :
      ( ~ l1_struct_0(X65)
      | k2_struct_0(X65) = u1_struct_0(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_54,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_55,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | k9_relat_1(X17,k1_relat_1(X17)) = k2_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk2_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_59,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_60,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k2_struct_0(esk3_0) = k2_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_38])])).

fof(c_0_62,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_63,plain,(
    ! [X27] :
      ( ( k2_relat_1(X27) = k1_relat_1(k2_funct_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) )
      & ( k1_relat_1(X27) = k2_relat_1(k2_funct_1(X27))
        | ~ v2_funct_1(X27)
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_64,plain,(
    ! [X20] :
      ( ( v1_relat_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) )
      & ( v1_funct_1(k2_funct_1(X20))
        | ~ v1_relat_1(X20)
        | ~ v1_funct_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_65,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_funct_1(X23)
      | ~ v2_funct_1(X23)
      | ~ r1_tarski(X24,k1_relat_1(X23))
      | k9_relat_1(k2_funct_1(X23),k9_relat_1(X23,X24)) = X24 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t177_funct_1])])])).

cnf(c_0_66,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])]),c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( k2_relat_1(esk4_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_58])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_71,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_72,plain,
    ( k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(esk4_0,u1_struct_0(esk2_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_44])])).

cnf(c_0_74,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_75,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_69])).

fof(c_0_76,plain,(
    ! [X64] :
      ( ( v1_funct_1(X64)
        | ~ v1_relat_1(X64)
        | ~ v1_funct_1(X64) )
      & ( v1_funct_2(X64,k1_relat_1(X64),k2_relat_1(X64))
        | ~ v1_relat_1(X64)
        | ~ v1_funct_1(X64) )
      & ( m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X64),k2_relat_1(X64))))
        | ~ v1_relat_1(X64)
        | ~ v1_funct_1(X64) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_77,plain,(
    ! [X18] :
      ( ( k1_relat_1(X18) != k1_xboole_0
        | k2_relat_1(X18) = k1_xboole_0
        | ~ v1_relat_1(X18) )
      & ( k2_relat_1(X18) != k1_xboole_0
        | k1_relat_1(X18) = k1_xboole_0
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_78,plain,
    ( k9_relat_1(k2_funct_1(X1),k2_relat_1(X1)) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_70]),c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_47]),c_0_44]),c_0_67]),c_0_75])])).

fof(c_0_80,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_81,plain,(
    ! [X58,X59,X60] :
      ( ( v1_funct_1(k2_funct_1(X60))
        | ~ v2_funct_1(X60)
        | k2_relset_1(X58,X59,X60) != X59
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X59)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( v1_funct_2(k2_funct_1(X60),X59,X58)
        | ~ v2_funct_1(X60)
        | k2_relset_1(X58,X59,X60) != X59
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X59)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( m1_subset_1(k2_funct_1(X60),k1_zfmisc_1(k2_zfmisc_1(X59,X58)))
        | ~ v2_funct_1(X60)
        | k2_relset_1(X58,X59,X60) != X59
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X59)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_83,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_84,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_85,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_68]),c_0_79]),c_0_74]),c_0_47]),c_0_44])])).

cnf(c_0_87,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_88,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_61]),c_0_68])).

cnf(c_0_90,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_71]),c_0_84])).

fof(c_0_91,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_93,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_46]),c_0_74]),c_0_47]),c_0_38])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_67]),c_0_74]),c_0_47]),c_0_44])])).

cnf(c_0_96,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_97,plain,(
    ! [X7,X8] :
      ( ~ v1_xboole_0(X7)
      | X7 = X8
      | ~ v1_xboole_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_98,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_92]),c_0_86]),c_0_93]),c_0_94])])).

cnf(c_0_100,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_101,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_95]),c_0_40])])).

cnf(c_0_102,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_103,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_104,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk4_0))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])])).

cnf(c_0_106,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_101])])).

cnf(c_0_107,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_102])).

cnf(c_0_108,plain,
    ( v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_70]),c_0_71])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_70]),c_0_68]),c_0_74]),c_0_47]),c_0_44])])).

cnf(c_0_110,negated_conjecture,
    ( X1 = k2_funct_1(esk4_0)
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k2_funct_1(esk4_0)),k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_106]),c_0_107]),c_0_94]),c_0_101])])).

cnf(c_0_112,negated_conjecture,
    ( v1_partfun1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))
    | ~ v4_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_68]),c_0_74]),c_0_47]),c_0_44])])).

cnf(c_0_113,negated_conjecture,
    ( v4_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_109])).

fof(c_0_114,plain,(
    ! [X61,X62,X63] :
      ( ( k5_relat_1(X63,k2_funct_1(X63)) = k6_partfun1(X61)
        | X62 = k1_xboole_0
        | k2_relset_1(X61,X62,X63) != X62
        | ~ v2_funct_1(X63)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X61,X62)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( k5_relat_1(k2_funct_1(X63),X63) = k6_partfun1(X62)
        | X62 = k1_xboole_0
        | k2_relset_1(X61,X62,X63) != X62
        | ~ v2_funct_1(X63)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X61,X62)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_115,plain,(
    ! [X50] : k6_partfun1(X50) = k6_relat_1(X50) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_116,plain,(
    ! [X42,X43,X44] :
      ( ( v1_funct_1(X44)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X43) )
      & ( ~ v1_xboole_0(X44)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X43) )
      & ( v1_funct_2(X44,X42,X43)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | v1_xboole_0(X42)
        | v1_xboole_0(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_117,plain,(
    ! [X19] :
      ( ~ v1_xboole_0(X19)
      | v1_funct_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_118,negated_conjecture,
    ( X1 = k2_funct_1(esk4_0)
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_101])])).

cnf(c_0_119,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(k2_funct_1(esk4_0)))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_111]),c_0_100])])).

cnf(c_0_120,negated_conjecture,
    ( v1_partfun1(k2_funct_1(esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113])])).

cnf(c_0_121,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_122,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_partfun1(X2)
    | X2 = k1_xboole_0
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_123,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_124,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_125,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_126,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk4_0)) = k2_funct_1(esk4_0)
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_127,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_113]),c_0_101])]),c_0_120])])).

cnf(c_0_128,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_83]),c_0_71]),c_0_84])).

fof(c_0_129,plain,(
    ! [X21] :
      ( v1_relat_1(k6_relat_1(X21))
      & v2_funct_1(k6_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

cnf(c_0_130,plain,
    ( X2 = k1_xboole_0
    | k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(X2)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(rw,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_131,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(csr,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_132,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_126]),c_0_127]),c_0_127]),c_0_94]),c_0_101])])).

cnf(c_0_133,negated_conjecture,
    ( v1_xboole_0(k2_funct_1(esk4_0))
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_101])])).

cnf(c_0_134,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_126]),c_0_127]),c_0_127]),c_0_94]),c_0_101])])).

fof(c_0_135,plain,(
    ! [X25,X26] :
      ( ( v2_funct_1(X26)
        | ~ v2_funct_1(k5_relat_1(X26,X25))
        | k2_relat_1(X26) != k1_relat_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( v2_funct_1(X25)
        | ~ v2_funct_1(k5_relat_1(X26,X25))
        | k2_relat_1(X26) != k1_relat_1(X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).

cnf(c_0_136,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_129])).

cnf(c_0_137,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk3_0)) = k5_relat_1(k2_funct_1(esk4_0),esk4_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_38]),c_0_89]),c_0_46]),c_0_74]),c_0_47])])).

fof(c_0_138,plain,(
    ! [X67,X68,X69] :
      ( ~ v1_funct_1(X69)
      | ~ v1_funct_2(X69,X67,X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))
      | k2_relset_1(X67,X68,X69) != X68
      | ~ v2_funct_1(X69)
      | k2_tops_2(X67,X68,X69) = k2_funct_1(X69) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_139,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133]),c_0_134])).

fof(c_0_140,plain,(
    ! [X22] :
      ( ( v1_relat_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X22) )
      & ( v1_funct_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X22) )
      & ( v2_funct_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v2_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_141,plain,
    ( v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X1,X2))
    | k2_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_142,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_funct_1(k5_relat_1(k2_funct_1(esk4_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_143,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_144,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_138])).

cnf(c_0_145,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_139]),c_0_58])]),c_0_59])).

cnf(c_0_146,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

cnf(c_0_147,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_68]),c_0_44])])).

cnf(c_0_148,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk4_0))
    | k2_relat_1(k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_67]),c_0_47]),c_0_94]),c_0_44])])).

cnf(c_0_149,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_144]),c_0_89]),c_0_46]),c_0_74]),c_0_47]),c_0_38])])).

cnf(c_0_150,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),k1_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_67]),c_0_74]),c_0_47]),c_0_44])])).

cnf(c_0_151,negated_conjecture,
    ( u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_146]),c_0_74]),c_0_47]),c_0_44])])).

cnf(c_0_152,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_147,c_0_67])).

cnf(c_0_153,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk4_0))
    | k2_relat_1(k2_funct_1(esk4_0)) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_71]),c_0_47]),c_0_44])])).

cnf(c_0_154,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_144]),c_0_94])])).

cnf(c_0_155,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_70]),c_0_68]),c_0_74]),c_0_47]),c_0_44])])).

fof(c_0_156,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | ~ v2_funct_1(X28)
      | k2_relat_1(X28) != k1_relat_1(X29)
      | k5_relat_1(X28,X29) != k6_relat_1(k1_relat_1(X28))
      | X29 = k2_funct_1(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).

cnf(c_0_157,negated_conjecture,
    ( u1_struct_0(esk3_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_151,c_0_152])).

cnf(c_0_158,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_83]),c_0_67]),c_0_74]),c_0_47]),c_0_44])])).

cnf(c_0_159,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_155])])).

cnf(c_0_160,plain,
    ( X2 = k2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v2_funct_1(X1)
    | k2_relat_1(X1) != k1_relat_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_156])).

cnf(c_0_161,negated_conjecture,
    ( k6_relat_1(u1_struct_0(esk3_0)) = k5_relat_1(k2_funct_1(esk4_0),esk4_0) ),
    inference(sr,[status(thm)],[c_0_137,c_0_157])).

cnf(c_0_162,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_158,c_0_157])).

cnf(c_0_163,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159,c_0_109])])).

cnf(c_0_164,negated_conjecture,
    ( X1 = k2_funct_1(k2_funct_1(esk4_0))
    | k5_relat_1(k2_funct_1(esk4_0),X1) != k5_relat_1(k2_funct_1(esk4_0),esk4_0)
    | k1_relat_1(X1) != u1_struct_0(esk2_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_127]),c_0_86]),c_0_94]),c_0_101])]),c_0_161]),c_0_162])])).

fof(c_0_165,plain,(
    ! [X51,X52,X53,X54] :
      ( ~ v1_funct_1(X53)
      | ~ v1_funct_2(X53,X51,X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,X51,X52)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | r2_funct_2(X51,X52,X53,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).

cnf(c_0_166,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_163,c_0_162])])).

cnf(c_0_167,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_164]),c_0_67]),c_0_47]),c_0_44])])).

cnf(c_0_168,plain,
    ( r2_funct_2(X2,X3,X1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_165])).

cnf(c_0_169,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_166,c_0_167])).

cnf(c_0_170,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),X1,X1)
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168,c_0_38]),c_0_46]),c_0_47])])).

cnf(c_0_171,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_46]),c_0_47]),c_0_38])])).

cnf(c_0_172,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_54]),c_0_86]),c_0_109])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.42  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.030 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t64_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 0.19/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.42  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.19/0.42  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.42  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.42  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.42  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.42  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.42  fof(t177_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v2_funct_1(X1)&r1_tarski(X2,k1_relat_1(X1)))=>k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 0.19/0.42  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.42  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.19/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.42  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.42  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.19/0.42  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.42  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 0.19/0.42  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.42  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.19/0.42  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.19/0.42  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.42  fof(t48_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(k5_relat_1(X2,X1))&k2_relat_1(X2)=k1_relat_1(X1))=>(v2_funct_1(X2)&v2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 0.19/0.42  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 0.19/0.42  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.19/0.42  fof(t63_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(((v2_funct_1(X1)&k2_relat_1(X1)=k1_relat_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>X2=k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 0.19/0.42  fof(reflexivity_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_funct_2(X1,X2,X3,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 0.19/0.42  fof(c_0_31, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3)))))), inference(assume_negation,[status(cth)],[t64_tops_2])).
% 0.19/0.42  fof(c_0_32, plain, ![X33, X34, X35]:((v4_relat_1(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(v5_relat_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.42  fof(c_0_33, negated_conjecture, (l1_struct_0(esk2_0)&((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&((k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0)&v2_funct_1(esk4_0))&~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).
% 0.19/0.42  fof(c_0_34, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.42  fof(c_0_35, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.42  fof(c_0_36, plain, ![X45, X46]:((~v1_partfun1(X46,X45)|k1_relat_1(X46)=X45|(~v1_relat_1(X46)|~v4_relat_1(X46,X45)))&(k1_relat_1(X46)!=X45|v1_partfun1(X46,X45)|(~v1_relat_1(X46)|~v4_relat_1(X46,X45)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.19/0.42  cnf(c_0_37, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_39, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.42  cnf(c_0_40, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  fof(c_0_41, plain, ![X39, X40, X41]:((v1_funct_1(X41)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_xboole_0(X40))&(v1_partfun1(X41,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_xboole_0(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.42  cnf(c_0_42, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  cnf(c_0_43, negated_conjecture, (v4_relat_1(esk4_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_40])])).
% 0.19/0.42  cnf(c_0_45, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  fof(c_0_48, plain, ![X36, X37, X38]:(~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|k2_relset_1(X36,X37,X38)=k2_relat_1(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.42  fof(c_0_49, plain, ![X66]:(v2_struct_0(X66)|~l1_struct_0(X66)|~v1_xboole_0(u1_struct_0(X66))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk2_0)|~v1_partfun1(esk4_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.19/0.42  cnf(c_0_51, negated_conjecture, (v1_partfun1(esk4_0,u1_struct_0(esk2_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_46]), c_0_47])])).
% 0.19/0.42  fof(c_0_52, plain, ![X65]:(~l1_struct_0(X65)|k2_struct_0(X65)=u1_struct_0(X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_54, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.42  fof(c_0_55, plain, ![X17]:(~v1_relat_1(X17)|k9_relat_1(X17,k1_relat_1(X17))=k2_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.42  cnf(c_0_56, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk2_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_60, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (k2_struct_0(esk3_0)=k2_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_38])])).
% 0.19/0.42  fof(c_0_62, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  fof(c_0_63, plain, ![X27]:((k2_relat_1(X27)=k1_relat_1(k2_funct_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))&(k1_relat_1(X27)=k2_relat_1(k2_funct_1(X27))|~v2_funct_1(X27)|(~v1_relat_1(X27)|~v1_funct_1(X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.42  fof(c_0_64, plain, ![X20]:((v1_relat_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))&(v1_funct_1(k2_funct_1(X20))|(~v1_relat_1(X20)|~v1_funct_1(X20)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.42  fof(c_0_65, plain, ![X23, X24]:(~v1_relat_1(X23)|~v1_funct_1(X23)|(~v2_funct_1(X23)|~r1_tarski(X24,k1_relat_1(X23))|k9_relat_1(k2_funct_1(X23),k9_relat_1(X23,X24))=X24)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t177_funct_1])])])).
% 0.19/0.42  cnf(c_0_66, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])]), c_0_59])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (k2_relat_1(esk4_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_58])])).
% 0.19/0.42  cnf(c_0_69, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.42  cnf(c_0_70, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.42  cnf(c_0_71, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.42  cnf(c_0_72, plain, (k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (k9_relat_1(esk4_0,u1_struct_0(esk2_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_44])])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_75, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_69])).
% 0.19/0.42  fof(c_0_76, plain, ![X64]:(((v1_funct_1(X64)|(~v1_relat_1(X64)|~v1_funct_1(X64)))&(v1_funct_2(X64,k1_relat_1(X64),k2_relat_1(X64))|(~v1_relat_1(X64)|~v1_funct_1(X64))))&(m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X64),k2_relat_1(X64))))|(~v1_relat_1(X64)|~v1_funct_1(X64)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.42  fof(c_0_77, plain, ![X18]:((k1_relat_1(X18)!=k1_xboole_0|k2_relat_1(X18)=k1_xboole_0|~v1_relat_1(X18))&(k2_relat_1(X18)!=k1_xboole_0|k1_relat_1(X18)=k1_xboole_0|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.19/0.42  cnf(c_0_78, plain, (k9_relat_1(k2_funct_1(X1),k2_relat_1(X1))=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_70]), c_0_71])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (k9_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_74]), c_0_47]), c_0_44]), c_0_67]), c_0_75])])).
% 0.19/0.42  fof(c_0_80, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.42  fof(c_0_81, plain, ![X58, X59, X60]:(((v1_funct_1(k2_funct_1(X60))|(~v2_funct_1(X60)|k2_relset_1(X58,X59,X60)!=X59)|(~v1_funct_1(X60)|~v1_funct_2(X60,X58,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))))&(v1_funct_2(k2_funct_1(X60),X59,X58)|(~v2_funct_1(X60)|k2_relset_1(X58,X59,X60)!=X59)|(~v1_funct_1(X60)|~v1_funct_2(X60,X58,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))))&(m1_subset_1(k2_funct_1(X60),k1_zfmisc_1(k2_zfmisc_1(X59,X58)))|(~v2_funct_1(X60)|k2_relset_1(X58,X59,X60)!=X59)|(~v1_funct_1(X60)|~v1_funct_2(X60,X58,X59)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.42  cnf(c_0_82, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.42  cnf(c_0_83, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.42  cnf(c_0_84, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.42  cnf(c_0_85, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_68]), c_0_79]), c_0_74]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_87, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.42  cnf(c_0_88, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.19/0.42  cnf(c_0_89, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_61]), c_0_68])).
% 0.19/0.42  cnf(c_0_90, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_71]), c_0_84])).
% 0.19/0.42  fof(c_0_91, plain, ![X11, X12]:(~v1_xboole_0(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.19/0.42  cnf(c_0_92, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.42  cnf(c_0_93, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_87])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_46]), c_0_74]), c_0_47]), c_0_38])])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_67]), c_0_74]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_96, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.42  fof(c_0_97, plain, ![X7, X8]:(~v1_xboole_0(X7)|X7=X8|~v1_xboole_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.42  cnf(c_0_98, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.42  cnf(c_0_99, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk2_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_92]), c_0_86]), c_0_93]), c_0_94])])).
% 0.19/0.42  cnf(c_0_100, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.42  cnf(c_0_101, negated_conjecture, (v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_95]), c_0_40])])).
% 0.19/0.42  cnf(c_0_102, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.42  cnf(c_0_103, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_96])).
% 0.19/0.42  cnf(c_0_104, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.19/0.42  cnf(c_0_105, negated_conjecture, (v1_xboole_0(k2_funct_1(esk4_0))|u1_struct_0(esk2_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])])).
% 0.19/0.42  cnf(c_0_106, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_101])])).
% 0.19/0.42  cnf(c_0_107, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_102])).
% 0.19/0.42  cnf(c_0_108, plain, (v1_partfun1(k2_funct_1(X1),k2_relat_1(X1))|~v4_relat_1(k2_funct_1(X1),k2_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_70]), c_0_71])).
% 0.19/0.42  cnf(c_0_109, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_70]), c_0_68]), c_0_74]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_110, negated_conjecture, (X1=k2_funct_1(esk4_0)|u1_struct_0(esk2_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk4_0))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.19/0.42  cnf(c_0_111, negated_conjecture, (m1_subset_1(k2_funct_1(k2_funct_1(esk4_0)),k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk2_0)!=k1_xboole_0|~v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_106]), c_0_107]), c_0_94]), c_0_101])])).
% 0.19/0.42  cnf(c_0_112, negated_conjecture, (v1_partfun1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))|~v4_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_68]), c_0_74]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_113, negated_conjecture, (v4_relat_1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_109])).
% 0.19/0.42  fof(c_0_114, plain, ![X61, X62, X63]:((k5_relat_1(X63,k2_funct_1(X63))=k6_partfun1(X61)|X62=k1_xboole_0|(k2_relset_1(X61,X62,X63)!=X62|~v2_funct_1(X63))|(~v1_funct_1(X63)|~v1_funct_2(X63,X61,X62)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))))&(k5_relat_1(k2_funct_1(X63),X63)=k6_partfun1(X62)|X62=k1_xboole_0|(k2_relset_1(X61,X62,X63)!=X62|~v2_funct_1(X63))|(~v1_funct_1(X63)|~v1_funct_2(X63,X61,X62)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.19/0.42  fof(c_0_115, plain, ![X50]:k6_partfun1(X50)=k6_relat_1(X50), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.42  fof(c_0_116, plain, ![X42, X43, X44]:(((v1_funct_1(X44)|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X43))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|(v1_xboole_0(X42)|v1_xboole_0(X43)))&(~v1_xboole_0(X44)|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X43))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|(v1_xboole_0(X42)|v1_xboole_0(X43))))&(v1_funct_2(X44,X42,X43)|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X43))|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|(v1_xboole_0(X42)|v1_xboole_0(X43)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.19/0.42  fof(c_0_117, plain, ![X19]:(~v1_xboole_0(X19)|v1_funct_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.19/0.42  cnf(c_0_118, negated_conjecture, (X1=k2_funct_1(esk4_0)|u1_struct_0(esk2_0)!=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_101])])).
% 0.19/0.42  cnf(c_0_119, negated_conjecture, (v1_xboole_0(k2_funct_1(k2_funct_1(esk4_0)))|u1_struct_0(esk2_0)!=k1_xboole_0|~v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_111]), c_0_100])])).
% 0.19/0.42  cnf(c_0_120, negated_conjecture, (v1_partfun1(k2_funct_1(esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113])])).
% 0.19/0.42  cnf(c_0_121, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.19/0.42  cnf(c_0_122, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_partfun1(X2)|X2=k1_xboole_0|k2_relset_1(X3,X2,X1)!=X2|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.19/0.42  cnf(c_0_123, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.19/0.42  cnf(c_0_124, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_116])).
% 0.19/0.42  cnf(c_0_125, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_117])).
% 0.19/0.42  cnf(c_0_126, negated_conjecture, (k2_funct_1(k2_funct_1(esk4_0))=k2_funct_1(esk4_0)|u1_struct_0(esk2_0)!=k1_xboole_0|~v2_funct_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_118, c_0_119])).
% 0.19/0.42  cnf(c_0_127, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_113]), c_0_101])]), c_0_120])])).
% 0.19/0.42  cnf(c_0_128, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_83]), c_0_71]), c_0_84])).
% 0.19/0.42  fof(c_0_129, plain, ![X21]:(v1_relat_1(k6_relat_1(X21))&v2_funct_1(k6_relat_1(X21))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.42  cnf(c_0_130, plain, (X2=k1_xboole_0|k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(X2)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(rw,[status(thm)],[c_0_122, c_0_123])).
% 0.19/0.42  cnf(c_0_131, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(csr,[status(thm)],[c_0_124, c_0_125])).
% 0.19/0.42  cnf(c_0_132, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0))))|u1_struct_0(esk2_0)!=k1_xboole_0|~v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_126]), c_0_127]), c_0_127]), c_0_94]), c_0_101])])).
% 0.19/0.42  cnf(c_0_133, negated_conjecture, (v1_xboole_0(k2_funct_1(esk4_0))|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_101])])).
% 0.19/0.42  cnf(c_0_134, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0))|u1_struct_0(esk2_0)!=k1_xboole_0|~v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_126]), c_0_127]), c_0_127]), c_0_94]), c_0_101])])).
% 0.19/0.42  fof(c_0_135, plain, ![X25, X26]:((v2_funct_1(X26)|(~v2_funct_1(k5_relat_1(X26,X25))|k2_relat_1(X26)!=k1_relat_1(X25))|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(v2_funct_1(X25)|(~v2_funct_1(k5_relat_1(X26,X25))|k2_relat_1(X26)!=k1_relat_1(X25))|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_1])])])])).
% 0.19/0.42  cnf(c_0_136, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_129])).
% 0.19/0.42  cnf(c_0_137, negated_conjecture, (k6_relat_1(u1_struct_0(esk3_0))=k5_relat_1(k2_funct_1(esk4_0),esk4_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_38]), c_0_89]), c_0_46]), c_0_74]), c_0_47])])).
% 0.19/0.42  fof(c_0_138, plain, ![X67, X68, X69]:(~v1_funct_1(X69)|~v1_funct_2(X69,X67,X68)|~m1_subset_1(X69,k1_zfmisc_1(k2_zfmisc_1(X67,X68)))|(k2_relset_1(X67,X68,X69)!=X68|~v2_funct_1(X69)|k2_tops_2(X67,X68,X69)=k2_funct_1(X69))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.19/0.42  cnf(c_0_139, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|u1_struct_0(esk2_0)!=k1_xboole_0|~v2_funct_1(k2_funct_1(esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_133]), c_0_134])).
% 0.19/0.42  fof(c_0_140, plain, ![X22]:(((v1_relat_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)|~v2_funct_1(X22)))&(v1_funct_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)|~v2_funct_1(X22))))&(v2_funct_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)|~v2_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.19/0.42  cnf(c_0_141, plain, (v2_funct_1(X1)|~v2_funct_1(k5_relat_1(X1,X2))|k2_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_135])).
% 0.19/0.42  cnf(c_0_142, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_funct_1(k5_relat_1(k2_funct_1(esk4_0),esk4_0))), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 0.19/0.42  cnf(c_0_143, negated_conjecture, (~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.42  cnf(c_0_144, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_138])).
% 0.19/0.42  cnf(c_0_145, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0|~v2_funct_1(k2_funct_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_139]), c_0_58])]), c_0_59])).
% 0.19/0.42  cnf(c_0_146, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_140])).
% 0.19/0.42  cnf(c_0_147, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|u1_struct_0(esk3_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_68]), c_0_44])])).
% 0.19/0.42  cnf(c_0_148, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk4_0))|k2_relat_1(k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_142]), c_0_67]), c_0_47]), c_0_94]), c_0_44])])).
% 0.19/0.42  cnf(c_0_149, negated_conjecture, (~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_143, c_0_144]), c_0_89]), c_0_46]), c_0_74]), c_0_47]), c_0_38])])).
% 0.19/0.42  cnf(c_0_150, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),k1_relat_1(k2_funct_1(esk4_0)),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_67]), c_0_74]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_151, negated_conjecture, (u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_146]), c_0_74]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_152, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|u1_struct_0(esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_147, c_0_67])).
% 0.19/0.42  cnf(c_0_153, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk4_0))|k2_relat_1(k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_71]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_154, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v2_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_144]), c_0_94])])).
% 0.19/0.42  cnf(c_0_155, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_70]), c_0_68]), c_0_74]), c_0_47]), c_0_44])])).
% 0.19/0.42  fof(c_0_156, plain, ![X28, X29]:(~v1_relat_1(X28)|~v1_funct_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)|(~v2_funct_1(X28)|k2_relat_1(X28)!=k1_relat_1(X29)|k5_relat_1(X28,X29)!=k6_relat_1(k1_relat_1(X28))|X29=k2_funct_1(X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_funct_1])])])).
% 0.19/0.42  cnf(c_0_157, negated_conjecture, (u1_struct_0(esk3_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_151, c_0_152])).
% 0.19/0.42  cnf(c_0_158, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_83]), c_0_67]), c_0_74]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_159, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)|~v2_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154, c_0_155])])).
% 0.19/0.42  cnf(c_0_160, plain, (X2=k2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v2_funct_1(X1)|k2_relat_1(X1)!=k1_relat_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_156])).
% 0.19/0.42  cnf(c_0_161, negated_conjecture, (k6_relat_1(u1_struct_0(esk3_0))=k5_relat_1(k2_funct_1(esk4_0),esk4_0)), inference(sr,[status(thm)],[c_0_137, c_0_157])).
% 0.19/0.42  cnf(c_0_162, negated_conjecture, (v2_funct_1(k2_funct_1(esk4_0))), inference(sr,[status(thm)],[c_0_158, c_0_157])).
% 0.19/0.42  cnf(c_0_163, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)|~v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_159, c_0_109])])).
% 0.19/0.42  cnf(c_0_164, negated_conjecture, (X1=k2_funct_1(k2_funct_1(esk4_0))|k5_relat_1(k2_funct_1(esk4_0),X1)!=k5_relat_1(k2_funct_1(esk4_0),esk4_0)|k1_relat_1(X1)!=u1_struct_0(esk2_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_127]), c_0_86]), c_0_94]), c_0_101])]), c_0_161]), c_0_162])])).
% 0.19/0.42  fof(c_0_165, plain, ![X51, X52, X53, X54]:(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|~v1_funct_1(X54)|~v1_funct_2(X54,X51,X52)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|r2_funct_2(X51,X52,X53,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).
% 0.19/0.42  cnf(c_0_166, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_163, c_0_162])])).
% 0.19/0.42  cnf(c_0_167, negated_conjecture, (k2_funct_1(k2_funct_1(esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_164]), c_0_67]), c_0_47]), c_0_44])])).
% 0.19/0.42  cnf(c_0_168, plain, (r2_funct_2(X2,X3,X1,X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_165])).
% 0.19/0.42  cnf(c_0_169, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk4_0)), inference(rw,[status(thm)],[c_0_166, c_0_167])).
% 0.19/0.42  cnf(c_0_170, negated_conjecture, (r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),X1,X1)|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_168, c_0_38]), c_0_46]), c_0_47])])).
% 0.19/0.42  cnf(c_0_171, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_170]), c_0_46]), c_0_47]), c_0_38])])).
% 0.19/0.42  cnf(c_0_172, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_171, c_0_54]), c_0_86]), c_0_109])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 173
% 0.19/0.42  # Proof object clause steps            : 111
% 0.19/0.42  # Proof object formula steps           : 62
% 0.19/0.42  # Proof object conjectures             : 69
% 0.19/0.42  # Proof object clause conjectures      : 66
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 43
% 0.19/0.42  # Proof object initial formulas used   : 31
% 0.19/0.42  # Proof object generating inferences   : 51
% 0.19/0.42  # Proof object simplifying inferences  : 172
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 34
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 69
% 0.19/0.42  # Removed in clause preprocessing      : 5
% 0.19/0.42  # Initial clauses in saturation        : 64
% 0.19/0.42  # Processed clauses                    : 642
% 0.19/0.42  # ...of these trivial                  : 16
% 0.19/0.42  # ...subsumed                          : 226
% 0.19/0.42  # ...remaining for further processing  : 400
% 0.19/0.42  # Other redundant clauses eliminated   : 7
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 36
% 0.19/0.42  # Backward-rewritten                   : 78
% 0.19/0.42  # Generated clauses                    : 889
% 0.19/0.42  # ...of the previous two non-trivial   : 751
% 0.19/0.42  # Contextual simplify-reflections      : 22
% 0.19/0.42  # Paramodulations                      : 872
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
% 0.19/0.42  # Current number of processed clauses  : 212
% 0.19/0.42  #    Positive orientable unit clauses  : 58
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 6
% 0.19/0.42  #    Non-unit-clauses                  : 148
% 0.19/0.42  # Current number of unprocessed clauses: 178
% 0.19/0.42  # ...number of literals in the above   : 1066
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 183
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 9645
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2490
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 234
% 0.19/0.42  # Unit Clause-clause subsumption calls : 256
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 23
% 0.19/0.42  # BW rewrite match successes           : 18
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 21174
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.074 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.078 s
% 0.19/0.42  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
