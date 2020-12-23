%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:13 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 285 expanded)
%              Number of clauses        :   57 (  95 expanded)
%              Number of leaves         :   14 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  438 (3787 expanded)
%              Number of equality atoms :   53 (  58 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ( ( v5_pre_topc(X4,X3,X2)
                              & r1_tmap_1(X2,X1,X5,X6) )
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( r2_hidden(X7,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k6_domain_1(u1_struct_0(X2),X6)))
                                 => r1_tmap_1(X3,X1,k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X4,X5),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tmap_1)).

fof(t52_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X3))
                             => ( ( X7 = k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)
                                  & r1_tmap_1(X2,X3,X4,X6)
                                  & r1_tmap_1(X3,X1,X5,X7) )
                               => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).

fof(t49_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t46_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( X2 != k1_xboole_0
       => ! [X5] :
            ( r2_hidden(X5,k8_relset_1(X1,X2,X4,X3))
          <=> ( r2_hidden(X5,X1)
              & r2_hidden(k1_funct_1(X4,X5),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_2)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(dt_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( ( v5_pre_topc(X4,X3,X2)
                                & r1_tmap_1(X2,X1,X5,X6) )
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( r2_hidden(X7,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k6_domain_1(u1_struct_0(X2),X6)))
                                   => r1_tmap_1(X3,X1,k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X4,X5),X7) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t53_tmap_1])).

fof(c_0_15,plain,(
    ! [X44,X45,X46,X47,X48,X49,X50] :
      ( v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | v2_struct_0(X46)
      | ~ v2_pre_topc(X46)
      | ~ l1_pre_topc(X46)
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X46))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))
      | ~ v1_funct_1(X48)
      | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X44))
      | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X44))))
      | ~ m1_subset_1(X49,u1_struct_0(X45))
      | ~ m1_subset_1(X50,u1_struct_0(X46))
      | X50 != k3_funct_2(u1_struct_0(X45),u1_struct_0(X46),X47,X49)
      | ~ r1_tmap_1(X45,X46,X47,X49)
      | ~ r1_tmap_1(X46,X44,X48,X50)
      | r1_tmap_1(X45,X44,k1_partfun1(u1_struct_0(X45),u1_struct_0(X46),u1_struct_0(X46),u1_struct_0(X44),X47,X48),X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    & m1_subset_1(esk8_0,u1_struct_0(esk4_0))
    & v5_pre_topc(esk6_0,esk5_0,esk4_0)
    & r1_tmap_1(esk4_0,esk3_0,esk7_0,esk8_0)
    & m1_subset_1(esk9_0,u1_struct_0(esk5_0))
    & r2_hidden(esk9_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk8_0)))
    & ~ r1_tmap_1(esk5_0,esk3_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk7_0),esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X39,X40,X41,X42] :
      ( ( ~ v5_pre_topc(X41,X40,X39)
        | ~ m1_subset_1(X42,u1_struct_0(X40))
        | r1_tmap_1(X40,X39,X41,X42)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X40))
        | v5_pre_topc(X41,X40,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ r1_tmap_1(X40,X39,X41,esk2_3(X39,X40,X41))
        | v5_pre_topc(X41,X40,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_18,plain,(
    ! [X37,X38] :
      ( v1_xboole_0(X37)
      | ~ m1_subset_1(X38,X37)
      | k6_domain_1(X37,X38) = k1_tarski(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | ~ m1_subset_1(X7,u1_struct_0(X3))
    | X7 != k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)
    | ~ r1_tmap_1(X2,X3,X4,X6)
    | ~ r1_tmap_1(X3,X1,X5,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( r1_tmap_1(X2,X3,X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_37,plain,(
    ! [X26,X27,X28,X29] :
      ( v1_xboole_0(X26)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,X26,X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | ~ m1_subset_1(X29,X26)
      | k3_funct_2(X26,X27,X28,X29) = k1_funct_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_38,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( ( r2_hidden(X34,X30)
        | ~ r2_hidden(X34,k8_relset_1(X30,X31,X33,X32))
        | X31 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( r2_hidden(k1_funct_1(X33,X34),X32)
        | ~ r2_hidden(X34,k8_relset_1(X30,X31,X33,X32))
        | X31 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( ~ r2_hidden(X34,X30)
        | ~ r2_hidden(k1_funct_1(X33,X34),X32)
        | r2_hidden(X34,k8_relset_1(X30,X31,X33,X32))
        | X31 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_funct_2])])])])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( r1_tmap_1(X1,esk3_0,k1_partfun1(u1_struct_0(X1),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),X2,esk7_0),X3)
    | v2_struct_0(X1)
    | X4 != k3_funct_2(u1_struct_0(X1),u1_struct_0(esk4_0),X2,X3)
    | ~ r1_tmap_1(esk4_0,esk3_0,esk7_0,X4)
    | ~ r1_tmap_1(X1,esk4_0,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X4,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_21]),c_0_32]),c_0_23]),c_0_33]),c_0_34]),c_0_35])]),c_0_27]),c_0_36])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | X5 = k1_xboole_0
    | ~ r2_hidden(X2,k8_relset_1(X4,X5,X1,X3))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X4,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk8_0) = k1_tarski(esk8_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

fof(c_0_47,plain,(
    ! [X15,X16] :
      ( ( k2_zfmisc_1(X15,X16) != k1_xboole_0
        | X15 = k1_xboole_0
        | X16 = k1_xboole_0 )
      & ( X15 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X15,X16) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk7_0),X1)
    | X2 != k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1)
    | ~ r1_tmap_1(esk4_0,esk3_0,esk7_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_30]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36]),c_0_42])).

fof(c_0_49,plain,(
    ! [X22,X23,X24,X25] :
      ( v1_xboole_0(X22)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,X22,X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ m1_subset_1(X25,X22)
      | m1_subset_1(k3_funct_2(X22,X23,X24,X25),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).

cnf(c_0_50,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1) = k1_funct_1(esk6_0,X1)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_34]),c_0_35])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_52,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,X1),X2)
    | ~ r2_hidden(X1,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_30]),c_0_34]),c_0_35])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk9_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,k1_tarski(esk8_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_55,plain,(
    ! [X19,X20,X21] :
      ( ( v1_funct_1(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | v1_xboole_0(X19)
        | v1_xboole_0(X20) )
      & ( ~ v1_xboole_0(X21)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | v1_xboole_0(X19)
        | v1_xboole_0(X20) )
      & ( v1_funct_2(X21,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | v1_xboole_0(X19)
        | v1_xboole_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).

fof(c_0_56,plain,(
    ! [X17,X18] :
      ( ~ v1_xboole_0(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(X17))
      | v1_xboole_0(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk3_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk7_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk7_0),X1)
    | ~ r1_tmap_1(esk4_0,esk3_0,esk7_0,k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk9_0) = k1_funct_1(esk6_0,esk9_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_62,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(esk4_0) = k1_xboole_0
    | r2_hidden(k1_funct_1(esk6_0,esk9_0),k1_tarski(esk8_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | u1_struct_0(esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_57])).

cnf(c_0_67,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_68,plain,(
    ! [X36] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | ~ v1_xboole_0(u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_69,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | l1_struct_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk3_0,esk7_0,k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk9_0))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk9_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_51])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(k1_funct_1(esk6_0,esk9_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_34]),c_0_35]),c_0_30]),c_0_51])])).

cnf(c_0_72,negated_conjecture,
    ( k1_funct_1(esk6_0,esk9_0) = X1
    | u1_struct_0(esk4_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_tarski(esk8_0) != k1_tarski(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_xboole_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_30]),c_0_34]),c_0_35])])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | u1_struct_0(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_75,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r1_tmap_1(esk4_0,esk3_0,esk7_0,k1_funct_1(esk6_0,esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_61]),c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(esk6_0,esk9_0) = esk8_0
    | u1_struct_0(esk4_0) = k1_xboole_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk3_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | u1_struct_0(esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])]),c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_33])]),c_0_36])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_83]),c_0_23])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:37:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.22/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.22/0.41  # and selection function PSelectComplexExceptRRHorn.
% 0.22/0.41  #
% 0.22/0.41  # Preprocessing time       : 0.030 s
% 0.22/0.41  # Presaturation interreduction done
% 0.22/0.41  
% 0.22/0.41  # Proof found!
% 0.22/0.41  # SZS status Theorem
% 0.22/0.41  # SZS output start CNFRefutation
% 0.22/0.41  fof(t53_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>((v5_pre_topc(X4,X3,X2)&r1_tmap_1(X2,X1,X5,X6))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(r2_hidden(X7,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k6_domain_1(u1_struct_0(X2),X6)))=>r1_tmap_1(X3,X1,k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X4,X5),X7)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_tmap_1)).
% 0.22/0.41  fof(t52_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X7=k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)&r1_tmap_1(X2,X3,X4,X6))&r1_tmap_1(X3,X1,X5,X7))=>r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tmap_1)).
% 0.22/0.41  fof(t49_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>r1_tmap_1(X2,X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 0.22/0.41  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.22/0.41  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.22/0.41  fof(t46_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(X2!=k1_xboole_0=>![X5]:(r2_hidden(X5,k8_relset_1(X1,X2,X4,X3))<=>(r2_hidden(X5,X1)&r2_hidden(k1_funct_1(X4,X5),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_funct_2)).
% 0.22/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.22/0.41  fof(dt_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 0.22/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.22/0.41  fof(cc6_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&~(v1_xboole_0(X3)))&v1_funct_2(X3,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 0.22/0.41  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.22/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.22/0.41  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.22/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.22/0.41  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>((v5_pre_topc(X4,X3,X2)&r1_tmap_1(X2,X1,X5,X6))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(r2_hidden(X7,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k6_domain_1(u1_struct_0(X2),X6)))=>r1_tmap_1(X3,X1,k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X4,X5),X7))))))))))), inference(assume_negation,[status(cth)],[t53_tmap_1])).
% 0.22/0.41  fof(c_0_15, plain, ![X44, X45, X46, X47, X48, X49, X50]:(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X46))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X46))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X44))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X44))))|(~m1_subset_1(X49,u1_struct_0(X45))|(~m1_subset_1(X50,u1_struct_0(X46))|(X50!=k3_funct_2(u1_struct_0(X45),u1_struct_0(X46),X47,X49)|~r1_tmap_1(X45,X46,X47,X49)|~r1_tmap_1(X46,X44,X48,X50)|r1_tmap_1(X45,X44,k1_partfun1(u1_struct_0(X45),u1_struct_0(X46),u1_struct_0(X46),u1_struct_0(X44),X47,X48),X49))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).
% 0.22/0.41  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&(m1_subset_1(esk8_0,u1_struct_0(esk4_0))&((v5_pre_topc(esk6_0,esk5_0,esk4_0)&r1_tmap_1(esk4_0,esk3_0,esk7_0,esk8_0))&(m1_subset_1(esk9_0,u1_struct_0(esk5_0))&(r2_hidden(esk9_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk8_0)))&~r1_tmap_1(esk5_0,esk3_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk7_0),esk9_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.22/0.41  fof(c_0_17, plain, ![X39, X40, X41, X42]:((~v5_pre_topc(X41,X40,X39)|(~m1_subset_1(X42,u1_struct_0(X40))|r1_tmap_1(X40,X39,X41,X42))|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&((m1_subset_1(esk2_3(X39,X40,X41),u1_struct_0(X40))|v5_pre_topc(X41,X40,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(~r1_tmap_1(X40,X39,X41,esk2_3(X39,X40,X41))|v5_pre_topc(X41,X40,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39)))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).
% 0.22/0.41  fof(c_0_18, plain, ![X37, X38]:(v1_xboole_0(X37)|~m1_subset_1(X38,X37)|k6_domain_1(X37,X38)=k1_tarski(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.22/0.41  cnf(c_0_19, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~m1_subset_1(X6,u1_struct_0(X2))|~m1_subset_1(X7,u1_struct_0(X3))|X7!=k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)|~r1_tmap_1(X2,X3,X4,X6)|~r1_tmap_1(X3,X1,X5,X7)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_29, plain, (r1_tmap_1(X2,X3,X1,X4)|v2_struct_0(X2)|v2_struct_0(X3)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.22/0.41  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_31, negated_conjecture, (v5_pre_topc(esk6_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  fof(c_0_37, plain, ![X26, X27, X28, X29]:(v1_xboole_0(X26)|~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|~m1_subset_1(X29,X26)|k3_funct_2(X26,X27,X28,X29)=k1_funct_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.22/0.41  fof(c_0_38, plain, ![X30, X31, X32, X33, X34]:(((r2_hidden(X34,X30)|~r2_hidden(X34,k8_relset_1(X30,X31,X33,X32))|X31=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(r2_hidden(k1_funct_1(X33,X34),X32)|~r2_hidden(X34,k8_relset_1(X30,X31,X33,X32))|X31=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(~r2_hidden(X34,X30)|~r2_hidden(k1_funct_1(X33,X34),X32)|r2_hidden(X34,k8_relset_1(X30,X31,X33,X32))|X31=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t46_funct_2])])])])).
% 0.22/0.41  cnf(c_0_39, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.22/0.41  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_41, negated_conjecture, (r1_tmap_1(X1,esk3_0,k1_partfun1(u1_struct_0(X1),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),X2,esk7_0),X3)|v2_struct_0(X1)|X4!=k3_funct_2(u1_struct_0(X1),u1_struct_0(esk4_0),X2,X3)|~r1_tmap_1(esk4_0,esk3_0,esk7_0,X4)|~r1_tmap_1(X1,esk4_0,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))|~m1_subset_1(X4,u1_struct_0(esk4_0))|~m1_subset_1(X3,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 0.22/0.41  cnf(c_0_42, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_21]), c_0_32]), c_0_23]), c_0_33]), c_0_34]), c_0_35])]), c_0_27]), c_0_36])).
% 0.22/0.41  cnf(c_0_43, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.22/0.41  cnf(c_0_44, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|X5=k1_xboole_0|~r2_hidden(X2,k8_relset_1(X4,X5,X1,X3))|~v1_funct_1(X1)|~v1_funct_2(X1,X4,X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.22/0.41  cnf(c_0_45, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_46, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk8_0)=k1_tarski(esk8_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.22/0.41  fof(c_0_47, plain, ![X15, X16]:((k2_zfmisc_1(X15,X16)!=k1_xboole_0|(X15=k1_xboole_0|X16=k1_xboole_0))&((X15!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0)&(X16!=k1_xboole_0|k2_zfmisc_1(X15,X16)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.22/0.41  cnf(c_0_48, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk7_0),X1)|X2!=k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1)|~r1_tmap_1(esk4_0,esk3_0,esk7_0,X2)|~m1_subset_1(X2,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_30]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36]), c_0_42])).
% 0.22/0.41  fof(c_0_49, plain, ![X22, X23, X24, X25]:(v1_xboole_0(X22)|~v1_funct_1(X24)|~v1_funct_2(X24,X22,X23)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|~m1_subset_1(X25,X22)|m1_subset_1(k3_funct_2(X22,X23,X24,X25),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).
% 0.22/0.41  cnf(c_0_50, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1)=k1_funct_1(esk6_0,X1)|v1_xboole_0(u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_34]), c_0_35])])).
% 0.22/0.41  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  fof(c_0_52, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.22/0.41  cnf(c_0_53, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,X1),X2)|~r2_hidden(X1,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_30]), c_0_34]), c_0_35])])).
% 0.22/0.41  cnf(c_0_54, negated_conjecture, (r2_hidden(esk9_0,k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,k1_tarski(esk8_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.22/0.41  fof(c_0_55, plain, ![X19, X20, X21]:(((v1_funct_1(X21)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|(v1_xboole_0(X19)|v1_xboole_0(X20)))&(~v1_xboole_0(X21)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|(v1_xboole_0(X19)|v1_xboole_0(X20))))&(v1_funct_2(X21,X19,X20)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|(v1_xboole_0(X19)|v1_xboole_0(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc6_funct_2])])])])])).
% 0.22/0.41  fof(c_0_56, plain, ![X17, X18]:(~v1_xboole_0(X17)|(~m1_subset_1(X18,k1_zfmisc_1(X17))|v1_xboole_0(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.22/0.41  cnf(c_0_57, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.22/0.41  cnf(c_0_58, negated_conjecture, (~r1_tmap_1(esk5_0,esk3_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk7_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_59, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk7_0),X1)|~r1_tmap_1(esk4_0,esk3_0,esk7_0,k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1))|~m1_subset_1(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,X1),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(er,[status(thm)],[c_0_48])).
% 0.22/0.41  cnf(c_0_60, plain, (v1_xboole_0(X1)|m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.22/0.41  cnf(c_0_61, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk9_0)=k1_funct_1(esk6_0,esk9_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.22/0.41  cnf(c_0_62, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.22/0.41  cnf(c_0_63, negated_conjecture, (u1_struct_0(esk4_0)=k1_xboole_0|r2_hidden(k1_funct_1(esk6_0,esk9_0),k1_tarski(esk8_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.22/0.41  cnf(c_0_64, plain, (v1_xboole_0(X2)|v1_xboole_0(X3)|~v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.22/0.41  cnf(c_0_65, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.22/0.41  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|u1_struct_0(esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_57])).
% 0.22/0.41  cnf(c_0_67, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.22/0.41  fof(c_0_68, plain, ![X36]:(v2_struct_0(X36)|~l1_struct_0(X36)|~v1_xboole_0(u1_struct_0(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.22/0.41  fof(c_0_69, plain, ![X35]:(~l1_pre_topc(X35)|l1_struct_0(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.22/0.41  cnf(c_0_70, negated_conjecture, (~r1_tmap_1(esk4_0,esk3_0,esk7_0,k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk9_0))|~m1_subset_1(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk6_0,esk9_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_51])])).
% 0.22/0.41  cnf(c_0_71, negated_conjecture, (m1_subset_1(k1_funct_1(esk6_0,esk9_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_34]), c_0_35]), c_0_30]), c_0_51])])).
% 0.22/0.41  cnf(c_0_72, negated_conjecture, (k1_funct_1(esk6_0,esk9_0)=X1|u1_struct_0(esk4_0)=k1_xboole_0|v1_xboole_0(u1_struct_0(esk4_0))|k1_tarski(esk8_0)!=k1_tarski(X1)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.22/0.41  cnf(c_0_73, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v1_xboole_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_30]), c_0_34]), c_0_35])])).
% 0.22/0.41  cnf(c_0_74, negated_conjecture, (v1_xboole_0(esk6_0)|u1_struct_0(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.22/0.41  cnf(c_0_75, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.22/0.41  cnf(c_0_76, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.22/0.41  cnf(c_0_77, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|~r1_tmap_1(esk4_0,esk3_0,esk7_0,k1_funct_1(esk6_0,esk9_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_61]), c_0_71])).
% 0.22/0.41  cnf(c_0_78, negated_conjecture, (k1_funct_1(esk6_0,esk9_0)=esk8_0|u1_struct_0(esk4_0)=k1_xboole_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(er,[status(thm)],[c_0_72])).
% 0.22/0.41  cnf(c_0_79, negated_conjecture, (r1_tmap_1(esk4_0,esk3_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.22/0.41  cnf(c_0_80, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))|u1_struct_0(esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.22/0.41  cnf(c_0_81, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.22/0.41  cnf(c_0_82, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])]), c_0_80])).
% 0.22/0.41  cnf(c_0_83, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_33])]), c_0_36])).
% 0.22/0.41  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_83]), c_0_23])]), c_0_27]), ['proof']).
% 0.22/0.41  # SZS output end CNFRefutation
% 0.22/0.41  # Proof object total steps             : 85
% 0.22/0.41  # Proof object clause steps            : 57
% 0.22/0.41  # Proof object formula steps           : 28
% 0.22/0.41  # Proof object conjectures             : 46
% 0.22/0.41  # Proof object clause conjectures      : 43
% 0.22/0.41  # Proof object formula conjectures     : 3
% 0.22/0.41  # Proof object initial clauses used    : 34
% 0.22/0.41  # Proof object initial formulas used   : 14
% 0.22/0.41  # Proof object generating inferences   : 23
% 0.22/0.41  # Proof object simplifying inferences  : 54
% 0.22/0.41  # Training examples: 0 positive, 0 negative
% 0.22/0.41  # Parsed axioms                        : 14
% 0.22/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.41  # Initial clauses                      : 45
% 0.22/0.41  # Removed in clause preprocessing      : 2
% 0.22/0.41  # Initial clauses in saturation        : 43
% 0.22/0.41  # Processed clauses                    : 264
% 0.22/0.41  # ...of these trivial                  : 1
% 0.22/0.41  # ...subsumed                          : 45
% 0.22/0.41  # ...remaining for further processing  : 218
% 0.22/0.41  # Other redundant clauses eliminated   : 5
% 0.22/0.41  # Clauses deleted for lack of memory   : 0
% 0.22/0.41  # Backward-subsumed                    : 12
% 0.22/0.41  # Backward-rewritten                   : 24
% 0.22/0.41  # Generated clauses                    : 256
% 0.22/0.41  # ...of the previous two non-trivial   : 228
% 0.22/0.41  # Contextual simplify-reflections      : 18
% 0.22/0.41  # Paramodulations                      : 225
% 0.22/0.41  # Factorizations                       : 18
% 0.22/0.41  # Equation resolutions                 : 13
% 0.22/0.41  # Propositional unsat checks           : 0
% 0.22/0.41  #    Propositional check models        : 0
% 0.22/0.41  #    Propositional check unsatisfiable : 0
% 0.22/0.41  #    Propositional clauses             : 0
% 0.22/0.41  #    Propositional clauses after purity: 0
% 0.22/0.41  #    Propositional unsat core size     : 0
% 0.22/0.41  #    Propositional preprocessing time  : 0.000
% 0.22/0.41  #    Propositional encoding time       : 0.000
% 0.22/0.41  #    Propositional solver time         : 0.000
% 0.22/0.41  #    Success case prop preproc time    : 0.000
% 0.22/0.41  #    Success case prop encoding time   : 0.000
% 0.22/0.41  #    Success case prop solver time     : 0.000
% 0.22/0.41  # Current number of processed clauses  : 138
% 0.22/0.41  #    Positive orientable unit clauses  : 20
% 0.22/0.41  #    Positive unorientable unit clauses: 0
% 0.22/0.41  #    Negative unit clauses             : 4
% 0.22/0.41  #    Non-unit-clauses                  : 114
% 0.22/0.41  # Current number of unprocessed clauses: 50
% 0.22/0.41  # ...number of literals in the above   : 327
% 0.22/0.41  # Current number of archived formulas  : 0
% 0.22/0.41  # Current number of archived clauses   : 79
% 0.22/0.41  # Clause-clause subsumption calls (NU) : 7828
% 0.22/0.41  # Rec. Clause-clause subsumption calls : 1177
% 0.22/0.41  # Non-unit clause-clause subsumptions  : 71
% 0.22/0.41  # Unit Clause-clause subsumption calls : 25
% 0.22/0.41  # Rewrite failures with RHS unbound    : 0
% 0.22/0.41  # BW rewrite match attempts            : 1
% 0.22/0.41  # BW rewrite match successes           : 1
% 0.22/0.41  # Condensation attempts                : 0
% 0.22/0.41  # Condensation successes               : 0
% 0.22/0.41  # Termbank termtop insertions          : 11750
% 0.22/0.41  
% 0.22/0.41  # -------------------------------------------------
% 0.22/0.41  # User time                : 0.054 s
% 0.22/0.41  # System time              : 0.005 s
% 0.22/0.41  # Total time               : 0.059 s
% 0.22/0.41  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
