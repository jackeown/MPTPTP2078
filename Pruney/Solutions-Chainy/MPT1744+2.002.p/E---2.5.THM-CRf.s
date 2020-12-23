%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:12 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 223 expanded)
%              Number of clauses        :   49 (  73 expanded)
%              Number of leaves         :   11 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  374 (2996 expanded)
%              Number of equality atoms :   44 (  44 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(d13_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( r2_hidden(X4,k1_relat_1(X1))
                & r2_hidden(k1_funct_1(X1,X4),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ v1_funct_1(X46)
      | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X43))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43))))
      | ~ m1_subset_1(X48,u1_struct_0(X44))
      | ~ m1_subset_1(X49,u1_struct_0(X45))
      | X49 != k3_funct_2(u1_struct_0(X44),u1_struct_0(X45),X46,X48)
      | ~ r1_tmap_1(X44,X45,X46,X48)
      | ~ r1_tmap_1(X45,X43,X47,X49)
      | r1_tmap_1(X44,X43,k1_partfun1(u1_struct_0(X44),u1_struct_0(X45),u1_struct_0(X45),u1_struct_0(X43),X46,X47),X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    & m1_subset_1(esk9_0,u1_struct_0(esk5_0))
    & v5_pre_topc(esk7_0,esk6_0,esk5_0)
    & r1_tmap_1(esk5_0,esk4_0,esk8_0,esk9_0)
    & m1_subset_1(esk10_0,u1_struct_0(esk6_0))
    & r2_hidden(esk10_0,k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,k6_domain_1(u1_struct_0(esk5_0),esk9_0)))
    & ~ r1_tmap_1(esk6_0,esk4_0,k1_partfun1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk7_0,esk8_0),esk10_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X38,X39,X40,X41] :
      ( ( ~ v5_pre_topc(X40,X39,X38)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | r1_tmap_1(X39,X38,X40,X41)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X39),u1_struct_0(X38))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38))))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk3_3(X38,X39,X40),u1_struct_0(X39))
        | v5_pre_topc(X40,X39,X38)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X39),u1_struct_0(X38))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38))))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ r1_tmap_1(X39,X38,X40,esk3_3(X38,X39,X40))
        | v5_pre_topc(X40,X39,X38)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,u1_struct_0(X39),u1_struct_0(X38))
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38))))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | v2_struct_0(X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_15,plain,(
    ! [X30,X31,X32,X33] :
      ( v1_xboole_0(X30)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,X30,X31)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ m1_subset_1(X33,X30)
      | k3_funct_2(X30,X31,X32,X33) = k1_funct_1(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_16,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_35,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] :
      ( ( r2_hidden(X18,k1_relat_1(X15))
        | ~ r2_hidden(X18,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(k1_funct_1(X15,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(X19,k1_relat_1(X15))
        | ~ r2_hidden(k1_funct_1(X15,X19),X16)
        | r2_hidden(X19,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( ~ r2_hidden(esk2_3(X15,X20,X21),X21)
        | ~ r2_hidden(esk2_3(X15,X20,X21),k1_relat_1(X15))
        | ~ r2_hidden(k1_funct_1(X15,esk2_3(X15,X20,X21)),X20)
        | X21 = k10_relat_1(X15,X20)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(esk2_3(X15,X20,X21),k1_relat_1(X15))
        | r2_hidden(esk2_3(X15,X20,X21),X21)
        | X21 = k10_relat_1(X15,X20)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( r2_hidden(k1_funct_1(X15,esk2_3(X15,X20,X21)),X20)
        | r2_hidden(esk2_3(X15,X20,X21),X21)
        | X21 = k10_relat_1(X15,X20)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).

fof(c_0_36,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k8_relset_1(X26,X27,X28,X29) = k10_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_37,plain,(
    ! [X36,X37] :
      ( v1_xboole_0(X36)
      | ~ m1_subset_1(X37,X36)
      | k6_domain_1(X36,X37) = k1_tarski(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_38,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k1_partfun1(u1_struct_0(X1),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),X2,esk8_0),X3)
    | v2_struct_0(X1)
    | X4 != k3_funct_2(u1_struct_0(X1),u1_struct_0(esk5_0),X2,X3)
    | ~ r1_tmap_1(esk5_0,esk4_0,esk8_0,X4)
    | ~ r1_tmap_1(X1,esk5_0,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk5_0))))
    | ~ m1_subset_1(X4,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_18]),c_0_29]),c_0_20]),c_0_30]),c_0_31]),c_0_32])]),c_0_24]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,X1) = k1_funct_1(esk7_0,X1)
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_31]),c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_42,plain,(
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

cnf(c_0_43,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X4 != k10_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk10_0,k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,k6_domain_1(u1_struct_0(esk5_0),esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_48,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_49,plain,(
    ! [X35] :
      ( v2_struct_0(X35)
      | ~ l1_struct_0(X35)
      | ~ v1_xboole_0(u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_50,plain,(
    ! [X34] :
      ( ~ l1_pre_topc(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk4_0,k1_partfun1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk7_0,esk8_0),X1)
    | X2 != k3_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,X1)
    | ~ r1_tmap_1(esk5_0,esk4_0,esk8_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_27]),c_0_29]),c_0_30]),c_0_31]),c_0_32])]),c_0_33]),c_0_39])).

cnf(c_0_52,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,esk10_0) = k1_funct_1(esk7_0,esk10_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tmap_1(esk6_0,esk4_0,k1_partfun1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk7_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( r2_hidden(k1_funct_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk10_0,k10_relat_1(esk7_0,k6_domain_1(u1_struct_0(esk5_0),esk9_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_27])])).

cnf(c_0_57,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk9_0) = k1_tarski(esk9_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | X1 != k1_funct_1(esk7_0,esk10_0)
    | ~ r1_tmap_1(esk5_0,esk4_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_41])]),c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk8_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,plain,
    ( k1_funct_1(X1,X2) = X3
    | X4 != k1_tarski(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X4)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(esk10_0,k10_relat_1(esk7_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_27])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | k1_funct_1(esk7_0,esk10_0) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_47])])).

cnf(c_0_68,negated_conjecture,
    ( k1_funct_1(esk7_0,esk10_0) = X1
    | v1_xboole_0(u1_struct_0(esk5_0))
    | k1_tarski(esk9_0) != k1_tarski(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_32]),c_0_65])])).

cnf(c_0_69,negated_conjecture,
    ( k1_funct_1(esk7_0,esk10_0) != esk9_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_30])]),c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_69])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_70]),c_0_20])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:53:15 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.17/0.37  # and selection function PSelectComplexExceptRRHorn.
% 0.17/0.37  #
% 0.17/0.37  # Preprocessing time       : 0.029 s
% 0.17/0.37  # Presaturation interreduction done
% 0.17/0.37  
% 0.17/0.37  # Proof found!
% 0.17/0.37  # SZS status Theorem
% 0.17/0.37  # SZS output start CNFRefutation
% 0.17/0.37  fof(t53_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>((v5_pre_topc(X4,X3,X2)&r1_tmap_1(X2,X1,X5,X6))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(r2_hidden(X7,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k6_domain_1(u1_struct_0(X2),X6)))=>r1_tmap_1(X3,X1,k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X4,X5),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tmap_1)).
% 0.17/0.37  fof(t52_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X7=k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)&r1_tmap_1(X2,X3,X4,X6))&r1_tmap_1(X3,X1,X5,X7))=>r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tmap_1)).
% 0.17/0.37  fof(t49_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>r1_tmap_1(X2,X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 0.17/0.37  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.17/0.37  fof(d13_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,k1_relat_1(X1))&r2_hidden(k1_funct_1(X1,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 0.17/0.37  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.17/0.37  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.17/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.17/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.17/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.17/0.37  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.17/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>((v5_pre_topc(X4,X3,X2)&r1_tmap_1(X2,X1,X5,X6))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(r2_hidden(X7,k8_relset_1(u1_struct_0(X3),u1_struct_0(X2),X4,k6_domain_1(u1_struct_0(X2),X6)))=>r1_tmap_1(X3,X1,k1_partfun1(u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X4,X5),X7))))))))))), inference(assume_negation,[status(cth)],[t53_tmap_1])).
% 0.17/0.37  fof(c_0_12, plain, ![X43, X44, X45, X46, X47, X48, X49]:(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))|(~v1_funct_1(X47)|~v1_funct_2(X47,u1_struct_0(X45),u1_struct_0(X43))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X43))))|(~m1_subset_1(X48,u1_struct_0(X44))|(~m1_subset_1(X49,u1_struct_0(X45))|(X49!=k3_funct_2(u1_struct_0(X44),u1_struct_0(X45),X46,X48)|~r1_tmap_1(X44,X45,X46,X48)|~r1_tmap_1(X45,X43,X47,X49)|r1_tmap_1(X44,X43,k1_partfun1(u1_struct_0(X44),u1_struct_0(X45),u1_struct_0(X45),u1_struct_0(X43),X46,X47),X48))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).
% 0.17/0.37  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))))&(m1_subset_1(esk9_0,u1_struct_0(esk5_0))&((v5_pre_topc(esk7_0,esk6_0,esk5_0)&r1_tmap_1(esk5_0,esk4_0,esk8_0,esk9_0))&(m1_subset_1(esk10_0,u1_struct_0(esk6_0))&(r2_hidden(esk10_0,k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,k6_domain_1(u1_struct_0(esk5_0),esk9_0)))&~r1_tmap_1(esk6_0,esk4_0,k1_partfun1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk7_0,esk8_0),esk10_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.17/0.37  fof(c_0_14, plain, ![X38, X39, X40, X41]:((~v5_pre_topc(X40,X39,X38)|(~m1_subset_1(X41,u1_struct_0(X39))|r1_tmap_1(X39,X38,X40,X41))|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X39),u1_struct_0(X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38)))))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&((m1_subset_1(esk3_3(X38,X39,X40),u1_struct_0(X39))|v5_pre_topc(X40,X39,X38)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X39),u1_struct_0(X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38)))))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(~r1_tmap_1(X39,X38,X40,esk3_3(X38,X39,X40))|v5_pre_topc(X40,X39,X38)|(~v1_funct_1(X40)|~v1_funct_2(X40,u1_struct_0(X39),u1_struct_0(X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38)))))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39))|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).
% 0.17/0.37  fof(c_0_15, plain, ![X30, X31, X32, X33]:(v1_xboole_0(X30)|~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|~m1_subset_1(X33,X30)|k3_funct_2(X30,X31,X32,X33)=k1_funct_1(X32,X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.17/0.37  cnf(c_0_16, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~m1_subset_1(X6,u1_struct_0(X2))|~m1_subset_1(X7,u1_struct_0(X3))|X7!=k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)|~r1_tmap_1(X2,X3,X4,X6)|~r1_tmap_1(X3,X1,X5,X7)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_26, plain, (r1_tmap_1(X2,X3,X1,X4)|v2_struct_0(X2)|v2_struct_0(X3)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_28, negated_conjecture, (v5_pre_topc(esk7_0,esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_34, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.37  fof(c_0_35, plain, ![X15, X16, X17, X18, X19, X20, X21]:((((r2_hidden(X18,k1_relat_1(X15))|~r2_hidden(X18,X17)|X17!=k10_relat_1(X15,X16)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(r2_hidden(k1_funct_1(X15,X18),X16)|~r2_hidden(X18,X17)|X17!=k10_relat_1(X15,X16)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&(~r2_hidden(X19,k1_relat_1(X15))|~r2_hidden(k1_funct_1(X15,X19),X16)|r2_hidden(X19,X17)|X17!=k10_relat_1(X15,X16)|(~v1_relat_1(X15)|~v1_funct_1(X15))))&((~r2_hidden(esk2_3(X15,X20,X21),X21)|(~r2_hidden(esk2_3(X15,X20,X21),k1_relat_1(X15))|~r2_hidden(k1_funct_1(X15,esk2_3(X15,X20,X21)),X20))|X21=k10_relat_1(X15,X20)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&((r2_hidden(esk2_3(X15,X20,X21),k1_relat_1(X15))|r2_hidden(esk2_3(X15,X20,X21),X21)|X21=k10_relat_1(X15,X20)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(r2_hidden(k1_funct_1(X15,esk2_3(X15,X20,X21)),X20)|r2_hidden(esk2_3(X15,X20,X21),X21)|X21=k10_relat_1(X15,X20)|(~v1_relat_1(X15)|~v1_funct_1(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_funct_1])])])])])])).
% 0.17/0.37  fof(c_0_36, plain, ![X26, X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k8_relset_1(X26,X27,X28,X29)=k10_relat_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.17/0.37  fof(c_0_37, plain, ![X36, X37]:(v1_xboole_0(X36)|~m1_subset_1(X37,X36)|k6_domain_1(X36,X37)=k1_tarski(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.17/0.37  cnf(c_0_38, negated_conjecture, (r1_tmap_1(X1,esk4_0,k1_partfun1(u1_struct_0(X1),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),X2,esk8_0),X3)|v2_struct_0(X1)|X4!=k3_funct_2(u1_struct_0(X1),u1_struct_0(esk5_0),X2,X3)|~r1_tmap_1(esk5_0,esk4_0,esk8_0,X4)|~r1_tmap_1(X1,esk5_0,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk5_0))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk5_0))))|~m1_subset_1(X4,u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(X1))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24]), c_0_25])).
% 0.17/0.37  cnf(c_0_39, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_18]), c_0_29]), c_0_20]), c_0_30]), c_0_31]), c_0_32])]), c_0_24]), c_0_33])).
% 0.17/0.37  cnf(c_0_40, negated_conjecture, (k3_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,X1)=k1_funct_1(esk7_0,X1)|v1_xboole_0(u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_31]), c_0_32])])).
% 0.17/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  fof(c_0_42, plain, ![X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X10,X9)|X10=X8|X9!=k1_tarski(X8))&(X11!=X8|r2_hidden(X11,X9)|X9!=k1_tarski(X8)))&((~r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)!=X12|X13=k1_tarski(X12))&(r2_hidden(esk1_2(X12,X13),X13)|esk1_2(X12,X13)=X12|X13=k1_tarski(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.17/0.37  cnf(c_0_43, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~r2_hidden(X2,X4)|X4!=k10_relat_1(X1,X3)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(esk10_0,k8_relset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,k6_domain_1(u1_struct_0(esk5_0),esk9_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_45, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.17/0.37  cnf(c_0_46, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.17/0.37  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  fof(c_0_48, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.17/0.37  fof(c_0_49, plain, ![X35]:(v2_struct_0(X35)|~l1_struct_0(X35)|~v1_xboole_0(u1_struct_0(X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.17/0.37  fof(c_0_50, plain, ![X34]:(~l1_pre_topc(X34)|l1_struct_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.17/0.37  cnf(c_0_51, negated_conjecture, (r1_tmap_1(esk6_0,esk4_0,k1_partfun1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk7_0,esk8_0),X1)|X2!=k3_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,X1)|~r1_tmap_1(esk5_0,esk4_0,esk8_0,X2)|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_27]), c_0_29]), c_0_30]), c_0_31]), c_0_32])]), c_0_33]), c_0_39])).
% 0.17/0.37  cnf(c_0_52, negated_conjecture, (k3_funct_2(u1_struct_0(esk6_0),u1_struct_0(esk5_0),esk7_0,esk10_0)=k1_funct_1(esk7_0,esk10_0)|v1_xboole_0(u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.17/0.37  cnf(c_0_53, negated_conjecture, (~r1_tmap_1(esk6_0,esk4_0,k1_partfun1(u1_struct_0(esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk4_0),esk7_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_54, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.17/0.37  cnf(c_0_55, plain, (r2_hidden(k1_funct_1(X1,X2),X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))), inference(er,[status(thm)],[c_0_43])).
% 0.17/0.37  cnf(c_0_56, negated_conjecture, (r2_hidden(esk10_0,k10_relat_1(esk7_0,k6_domain_1(u1_struct_0(esk5_0),esk9_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_27])])).
% 0.17/0.37  cnf(c_0_57, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk9_0)=k1_tarski(esk9_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.17/0.37  cnf(c_0_58, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.17/0.37  cnf(c_0_59, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.17/0.37  cnf(c_0_60, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.17/0.37  cnf(c_0_61, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|X1!=k1_funct_1(esk7_0,esk10_0)|~r1_tmap_1(esk5_0,esk4_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_41])]), c_0_53])).
% 0.17/0.37  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk8_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.37  cnf(c_0_63, plain, (k1_funct_1(X1,X2)=X3|X4!=k1_tarski(X3)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X4))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.17/0.37  cnf(c_0_64, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|r2_hidden(esk10_0,k10_relat_1(esk7_0,k1_tarski(esk9_0)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.17/0.37  cnf(c_0_65, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_27])).
% 0.17/0.37  cnf(c_0_66, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.17/0.37  cnf(c_0_67, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|k1_funct_1(esk7_0,esk10_0)!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_47])])).
% 0.17/0.37  cnf(c_0_68, negated_conjecture, (k1_funct_1(esk7_0,esk10_0)=X1|v1_xboole_0(u1_struct_0(esk5_0))|k1_tarski(esk9_0)!=k1_tarski(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_32]), c_0_65])])).
% 0.17/0.37  cnf(c_0_69, negated_conjecture, (k1_funct_1(esk7_0,esk10_0)!=esk9_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_30])]), c_0_33])).
% 0.17/0.37  cnf(c_0_70, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(er,[status(thm)],[c_0_68]), c_0_69])).
% 0.17/0.37  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_70]), c_0_20])]), c_0_24]), ['proof']).
% 0.17/0.37  # SZS output end CNFRefutation
% 0.17/0.37  # Proof object total steps             : 72
% 0.17/0.37  # Proof object clause steps            : 49
% 0.17/0.37  # Proof object formula steps           : 23
% 0.17/0.37  # Proof object conjectures             : 39
% 0.17/0.37  # Proof object clause conjectures      : 36
% 0.17/0.37  # Proof object formula conjectures     : 3
% 0.17/0.37  # Proof object initial clauses used    : 31
% 0.17/0.37  # Proof object initial formulas used   : 11
% 0.17/0.37  # Proof object generating inferences   : 18
% 0.17/0.37  # Proof object simplifying inferences  : 46
% 0.17/0.37  # Training examples: 0 positive, 0 negative
% 0.17/0.37  # Parsed axioms                        : 11
% 0.17/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.37  # Initial clauses                      : 41
% 0.17/0.37  # Removed in clause preprocessing      : 0
% 0.17/0.37  # Initial clauses in saturation        : 41
% 0.17/0.37  # Processed clauses                    : 146
% 0.17/0.37  # ...of these trivial                  : 2
% 0.17/0.37  # ...subsumed                          : 5
% 0.17/0.37  # ...remaining for further processing  : 139
% 0.17/0.37  # Other redundant clauses eliminated   : 3
% 0.17/0.37  # Clauses deleted for lack of memory   : 0
% 0.17/0.37  # Backward-subsumed                    : 2
% 0.17/0.37  # Backward-rewritten                   : 9
% 0.17/0.37  # Generated clauses                    : 222
% 0.17/0.37  # ...of the previous two non-trivial   : 213
% 0.17/0.37  # Contextual simplify-reflections      : 2
% 0.17/0.37  # Paramodulations                      : 204
% 0.17/0.37  # Factorizations                       : 5
% 0.17/0.37  # Equation resolutions                 : 13
% 0.17/0.37  # Propositional unsat checks           : 0
% 0.17/0.37  #    Propositional check models        : 0
% 0.17/0.37  #    Propositional check unsatisfiable : 0
% 0.17/0.37  #    Propositional clauses             : 0
% 0.17/0.37  #    Propositional clauses after purity: 0
% 0.17/0.37  #    Propositional unsat core size     : 0
% 0.17/0.37  #    Propositional preprocessing time  : 0.000
% 0.17/0.37  #    Propositional encoding time       : 0.000
% 0.17/0.37  #    Propositional solver time         : 0.000
% 0.17/0.37  #    Success case prop preproc time    : 0.000
% 0.17/0.37  #    Success case prop encoding time   : 0.000
% 0.17/0.37  #    Success case prop solver time     : 0.000
% 0.17/0.37  # Current number of processed clauses  : 86
% 0.17/0.37  #    Positive orientable unit clauses  : 24
% 0.17/0.37  #    Positive unorientable unit clauses: 0
% 0.17/0.37  #    Negative unit clauses             : 5
% 0.17/0.37  #    Non-unit-clauses                  : 57
% 0.17/0.37  # Current number of unprocessed clauses: 145
% 0.17/0.37  # ...number of literals in the above   : 1154
% 0.17/0.37  # Current number of archived formulas  : 0
% 0.17/0.37  # Current number of archived clauses   : 52
% 0.17/0.37  # Clause-clause subsumption calls (NU) : 2452
% 0.17/0.37  # Rec. Clause-clause subsumption calls : 206
% 0.17/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.17/0.37  # Unit Clause-clause subsumption calls : 38
% 0.17/0.37  # Rewrite failures with RHS unbound    : 0
% 0.17/0.37  # BW rewrite match attempts            : 3
% 0.17/0.37  # BW rewrite match successes           : 3
% 0.17/0.37  # Condensation attempts                : 0
% 0.17/0.37  # Condensation successes               : 0
% 0.17/0.37  # Termbank termtop insertions          : 9677
% 0.17/0.37  
% 0.17/0.37  # -------------------------------------------------
% 0.17/0.37  # User time                : 0.041 s
% 0.17/0.37  # System time              : 0.006 s
% 0.17/0.37  # Total time               : 0.047 s
% 0.17/0.37  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
