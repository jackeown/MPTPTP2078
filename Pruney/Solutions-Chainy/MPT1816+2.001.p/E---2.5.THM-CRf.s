%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:32 EST 2020

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  100 (6914 expanded)
%              Number of clauses        :   77 (2174 expanded)
%              Number of leaves         :   10 (1715 expanded)
%              Depth                    :   18
%              Number of atoms          :  638 (198002 expanded)
%              Number of equality atoms :   17 (4505 expanded)
%              Maximal formula depth    :   49 (   6 average)
%              Maximal clause size      :   91 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t132_tmap_1,conjecture,(
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
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( X1 = k1_tsep_1(X1,X4,X5)
                          & r4_tsep_1(X1,X4,X5) )
                       => ( ( v1_funct_1(X3)
                            & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                            & v5_pre_topc(X3,X1,X2)
                            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                            & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(d4_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

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

fof(t129_tmap_1,axiom,(
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
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                        <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
                            & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
                            & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
                            & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
                            & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( X1 = k1_tsep_1(X1,X4,X5)
                            & r4_tsep_1(X1,X4,X5) )
                         => ( ( v1_funct_1(X3)
                              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                              & v5_pre_topc(X3,X1,X2)
                              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                          <=> ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
                              & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
                              & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
                              & v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
                              & v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
                              & v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
                              & m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t132_tmap_1])).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ v1_funct_1(X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k2_partfun1(X19,X20,X21,X22) = k7_relat_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0)
    & r4_tsep_1(esk1_0,esk4_0,esk5_0)
    & ( ~ v1_funct_1(esk3_0)
      | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
      | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_1(esk3_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_1(esk3_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_1(esk3_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_1(esk3_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_1(esk3_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | v5_pre_topc(esk3_0,esk1_0,esk2_0) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) )
    & ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
      | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_12,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
    <=> ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    introduced(definition)).

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
      | ~ m1_pre_topc(X33,X30)
      | k2_tmap_1(X30,X31,X32,X33) = k2_partfun1(u1_struct_0(X30),u1_struct_0(X31),X32,u1_struct_0(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_14,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_18,plain,(
    ! [X12,X13] : v1_relat_1(k2_zfmisc_1(X12,X13)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_19,axiom,(
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
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( r4_tsep_1(X1,X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => epred1_5(X2,X3,X4,X5,X1) ) ) ) ) ) ) ),
    inference(apply_def,[status(thm)],[t129_tmap_1,c_0_12])).

fof(c_0_20,plain,(
    ! [X1,X5,X4,X3,X2] :
      ( epred1_5(X2,X3,X4,X5,X1)
     => ( ( v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
      <=> ( v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
          & v1_funct_1(k2_tmap_1(X1,X2,X5,X4))
          & v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2))
          & v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2)
          & m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_12])).

fof(c_0_21,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v4_relat_1(X15,X14)
      | X15 = k7_relat_1(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_31,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_33,plain,(
    ! [X16,X17,X18] :
      ( ( v4_relat_1(X18,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v5_relat_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_34,plain,(
    ! [X53] :
      ( ~ l1_pre_topc(X53)
      | m1_pre_topc(X53,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

fof(c_0_35,plain,(
    ! [X41,X42,X43,X44,X45] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | v2_struct_0(X43)
      | ~ m1_pre_topc(X43,X41)
      | v2_struct_0(X44)
      | ~ m1_pre_topc(X44,X41)
      | ~ r4_tsep_1(X41,X43,X44)
      | ~ v1_funct_1(X45)
      | ~ v1_funct_2(X45,u1_struct_0(X41),u1_struct_0(X42))
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
      | epred1_5(X42,X43,X44,X45,X41) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_36,plain,(
    ! [X62,X63,X64,X65,X66] :
      ( ( v1_funct_1(k2_tmap_1(X62,X66,X63,X65))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( v1_funct_1(k2_tmap_1(X62,X66,X63,X64))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66))))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,X65))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,X64))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,X65))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,X64))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,X65))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,X64))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) )
      & ( m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,X65))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | ~ v1_funct_1(k2_tmap_1(X62,X66,X63,X64))
        | ~ v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))
        | ~ v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)
        | ~ m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66))))
        | ~ epred1_5(X66,X65,X64,X63,X62) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_37,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_15]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_16])]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_15]),c_0_32])])).

cnf(c_0_40,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | epred1_5(X2,X3,X4,X5,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ r4_tsep_1(X1,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,X1) = esk3_0
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ v4_relat_1(esk3_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_46,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_25])).

cnf(c_0_48,negated_conjecture,
    ( epred1_5(esk2_0,X1,X2,esk3_0,esk1_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r4_tsep_1(esk1_0,X1,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_15]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_16])]),c_0_28]),c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( r4_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_funct_1(esk3_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk5_0))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])]),c_0_52]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_59,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X5,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_60,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_16]),c_0_23]),c_0_15])])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_23]),c_0_16]),c_0_15])]),c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk4_0))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_44])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_64,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_56]),c_0_57]),c_0_23]),c_0_16]),c_0_15])]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_44])).

cnf(c_0_68,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_69,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X5,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_70,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_71,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_56]),c_0_57]),c_0_23]),c_0_16]),c_0_15])]),c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_44])).

cnf(c_0_73,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_74,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71])])).

cnf(c_0_76,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_56]),c_0_57]),c_0_23]),c_0_16]),c_0_15])]),c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_44])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_79,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X5,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_80,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_76])])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_56]),c_0_57]),c_0_23]),c_0_16]),c_0_15])]),c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_44])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_84,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_56]),c_0_57]),c_0_23]),c_0_16]),c_0_15])]),c_0_83])).

cnf(c_0_86,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_87,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_44])).

cnf(c_0_89,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X5,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_90,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_57]),c_0_56]),c_0_56]),c_0_23]),c_0_56]),c_0_16]),c_0_56]),c_0_15])])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_44])).

cnf(c_0_92,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X5))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X5,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_94,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_57]),c_0_56]),c_0_56]),c_0_23]),c_0_56]),c_0_16]),c_0_56]),c_0_15])])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_96,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X1))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk5_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_92,c_0_44])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[c_0_95,c_0_94])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_56]),c_0_57]),c_0_71]),c_0_76]),c_0_81]),c_0_85]),c_0_61]),c_0_66]),c_0_98])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:28:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.79/0.94  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.79/0.94  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.79/0.94  #
% 0.79/0.94  # Preprocessing time       : 0.032 s
% 0.79/0.94  # Presaturation interreduction done
% 0.79/0.94  
% 0.79/0.94  # Proof found!
% 0.79/0.94  # SZS status Theorem
% 0.79/0.94  # SZS output start CNFRefutation
% 0.79/0.94  fof(t132_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((X1=k1_tsep_1(X1,X4,X5)&r4_tsep_1(X1,X4,X5))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_tmap_1)).
% 0.79/0.94  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.79/0.94  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.79/0.94  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.79/0.94  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.79/0.94  fof(t129_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_tmap_1)).
% 0.79/0.94  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.79/0.94  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.79/0.94  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.79/0.94  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((X1=k1_tsep_1(X1,X4,X5)&r4_tsep_1(X1,X4,X5))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))))))))))), inference(assume_negation,[status(cth)],[t132_tmap_1])).
% 0.79/0.94  fof(c_0_10, plain, ![X19, X20, X21, X22]:(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k2_partfun1(X19,X20,X21,X22)=k7_relat_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.79/0.94  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&r4_tsep_1(esk1_0,esk4_0,esk5_0))&((~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|(~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))))&(((((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_1(esk3_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_1(esk3_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.79/0.94  fof(c_0_12, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)<=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), introduced(definition)).
% 0.79/0.94  fof(c_0_13, plain, ![X30, X31, X32, X33]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))|(~m1_pre_topc(X33,X30)|k2_tmap_1(X30,X31,X32,X33)=k2_partfun1(u1_struct_0(X30),u1_struct_0(X31),X32,u1_struct_0(X33)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.79/0.94  cnf(c_0_14, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.79/0.94  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  fof(c_0_17, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.79/0.94  fof(c_0_18, plain, ![X12, X13]:v1_relat_1(k2_zfmisc_1(X12,X13)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.79/0.94  fof(c_0_19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>epred1_5(X2,X3,X4,X5,X1))))))), inference(apply_def,[status(thm)],[t129_tmap_1, c_0_12])).
% 0.79/0.94  fof(c_0_20, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), inference(split_equiv,[status(thm)],[c_0_12])).
% 0.79/0.94  fof(c_0_21, plain, ![X14, X15]:(~v1_relat_1(X15)|~v4_relat_1(X15,X14)|X15=k7_relat_1(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.79/0.94  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.79/0.94  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_30, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.79/0.94  cnf(c_0_31, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.79/0.94  cnf(c_0_32, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.79/0.94  fof(c_0_33, plain, ![X16, X17, X18]:((v4_relat_1(X18,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(v5_relat_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.79/0.94  fof(c_0_34, plain, ![X53]:(~l1_pre_topc(X53)|m1_pre_topc(X53,X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.79/0.94  fof(c_0_35, plain, ![X41, X42, X43, X44, X45]:(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|(v2_struct_0(X43)|~m1_pre_topc(X43,X41)|(v2_struct_0(X44)|~m1_pre_topc(X44,X41)|(~r4_tsep_1(X41,X43,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(X41),u1_struct_0(X42))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))|epred1_5(X42,X43,X44,X45,X41))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.79/0.94  fof(c_0_36, plain, ![X62, X63, X64, X65, X66]:(((((((((v1_funct_1(k2_tmap_1(X62,X66,X63,X65))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|~v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62))&(v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|~v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&(v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)|(~v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|~v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&(m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|~v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&(v1_funct_1(k2_tmap_1(X62,X66,X63,X64))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|~v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&(v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|~v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&(v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)|(~v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|~v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&(m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66))))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|~v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&((((v1_funct_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,X65))|~v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))|~v1_funct_1(k2_tmap_1(X62,X66,X63,X64))|~v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62))&(v1_funct_2(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,X65))|~v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))|~v1_funct_1(k2_tmap_1(X62,X66,X63,X64))|~v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&(v5_pre_topc(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_tsep_1(X62,X65,X64),X66)|(~v1_funct_1(k2_tmap_1(X62,X66,X63,X65))|~v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))|~v1_funct_1(k2_tmap_1(X62,X66,X63,X64))|~v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))&(m1_subset_1(k2_tmap_1(X62,X66,X63,k1_tsep_1(X62,X65,X64)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X62,X65,X64)),u1_struct_0(X66))))|(~v1_funct_1(k2_tmap_1(X62,X66,X63,X65))|~v1_funct_2(k2_tmap_1(X62,X66,X63,X65),u1_struct_0(X65),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,X65),X65,X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,X65),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))|~v1_funct_1(k2_tmap_1(X62,X66,X63,X64))|~v1_funct_2(k2_tmap_1(X62,X66,X63,X64),u1_struct_0(X64),u1_struct_0(X66))|~v5_pre_topc(k2_tmap_1(X62,X66,X63,X64),X64,X66)|~m1_subset_1(k2_tmap_1(X62,X66,X63,X64),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X66)))))|~epred1_5(X66,X65,X64,X63,X62)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.79/0.94  cnf(c_0_37, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.79/0.94  cnf(c_0_38, negated_conjecture, (k7_relat_1(esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_15]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_16])]), c_0_28]), c_0_29]), c_0_30])).
% 0.79/0.94  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_15]), c_0_32])])).
% 0.79/0.94  cnf(c_0_40, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.79/0.94  cnf(c_0_41, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.79/0.94  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|epred1_5(X2,X3,X4,X5,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.79/0.94  cnf(c_0_43, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))|~epred1_5(X2,X5,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_44, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_45, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)=esk3_0|~m1_pre_topc(X1,esk1_0)|~v4_relat_1(esk3_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 0.79/0.94  cnf(c_0_46, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_40, c_0_15])).
% 0.79/0.94  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_41, c_0_25])).
% 0.79/0.94  cnf(c_0_48, negated_conjecture, (epred1_5(esk2_0,X1,X2,esk3_0,esk1_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r4_tsep_1(esk1_0,X1,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_15]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_16])]), c_0_28]), c_0_29])).
% 0.79/0.94  cnf(c_0_49, negated_conjecture, (r4_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_51, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_54, negated_conjecture, (~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_55, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk5_0))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.79/0.94  cnf(c_0_56, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.79/0.94  cnf(c_0_57, negated_conjecture, (epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])]), c_0_52]), c_0_53])).
% 0.79/0.94  cnf(c_0_58, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_59, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_60, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_16]), c_0_23]), c_0_15])])).
% 0.79/0.94  cnf(c_0_61, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_23]), c_0_16]), c_0_15])]), c_0_58])).
% 0.79/0.94  cnf(c_0_62, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk4_0))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_59, c_0_44])).
% 0.79/0.94  cnf(c_0_63, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_64, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))|~epred1_5(X2,X5,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_65, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 0.79/0.94  cnf(c_0_66, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_56]), c_0_57]), c_0_23]), c_0_16]), c_0_15])]), c_0_63])).
% 0.79/0.94  cnf(c_0_67, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_64, c_0_44])).
% 0.79/0.94  cnf(c_0_68, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_69, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_70, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.79/0.94  cnf(c_0_71, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_56]), c_0_57]), c_0_23]), c_0_16]), c_0_15])]), c_0_68])).
% 0.79/0.94  cnf(c_0_72, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_69, c_0_44])).
% 0.79/0.94  cnf(c_0_73, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_74, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))|~epred1_5(X2,X5,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_75, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71])])).
% 0.79/0.94  cnf(c_0_76, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_56]), c_0_57]), c_0_23]), c_0_16]), c_0_15])]), c_0_73])).
% 0.79/0.94  cnf(c_0_77, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X1))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_74, c_0_44])).
% 0.79/0.94  cnf(c_0_78, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_79, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_80, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_76])])).
% 0.79/0.94  cnf(c_0_81, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_56]), c_0_57]), c_0_23]), c_0_16]), c_0_15])]), c_0_78])).
% 0.79/0.94  cnf(c_0_82, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X1))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_79, c_0_44])).
% 0.79/0.94  cnf(c_0_83, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_84, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.79/0.94  cnf(c_0_85, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_56]), c_0_57]), c_0_23]), c_0_16]), c_0_15])]), c_0_83])).
% 0.79/0.94  cnf(c_0_86, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))|~epred1_5(X2,X5,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_87, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 0.79/0.94  cnf(c_0_88, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_86, c_0_44])).
% 0.79/0.94  cnf(c_0_89, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_90, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_57]), c_0_56]), c_0_56]), c_0_23]), c_0_56]), c_0_16]), c_0_56]), c_0_15])])).
% 0.79/0.94  cnf(c_0_91, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_89, c_0_44])).
% 0.79/0.94  cnf(c_0_92, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(k2_tmap_1(X1,X2,X3,X5))|~v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.79/0.94  cnf(c_0_93, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_94, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_57]), c_0_56]), c_0_56]), c_0_23]), c_0_56]), c_0_16]), c_0_56]), c_0_15])])).
% 0.79/0.94  cnf(c_0_95, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.79/0.94  cnf(c_0_96, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk5_0))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk4_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_92, c_0_44])).
% 0.79/0.94  cnf(c_0_97, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[c_0_93, c_0_94])).
% 0.79/0.94  cnf(c_0_98, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[c_0_95, c_0_94])).
% 0.79/0.94  cnf(c_0_99, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_56]), c_0_57]), c_0_71]), c_0_76]), c_0_81]), c_0_85]), c_0_61]), c_0_66]), c_0_98])]), c_0_94]), ['proof']).
% 0.79/0.94  # SZS output end CNFRefutation
% 0.79/0.94  # Proof object total steps             : 100
% 0.79/0.94  # Proof object clause steps            : 77
% 0.79/0.94  # Proof object formula steps           : 23
% 0.79/0.94  # Proof object conjectures             : 63
% 0.79/0.94  # Proof object clause conjectures      : 60
% 0.79/0.94  # Proof object formula conjectures     : 3
% 0.79/0.94  # Proof object initial clauses used    : 41
% 0.79/0.94  # Proof object initial formulas used   : 9
% 0.79/0.94  # Proof object generating inferences   : 27
% 0.79/0.94  # Proof object simplifying inferences  : 115
% 0.79/0.94  # Training examples: 0 positive, 0 negative
% 0.79/0.94  # Parsed axioms                        : 20
% 0.79/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.79/0.94  # Initial clauses                      : 87
% 0.79/0.94  # Removed in clause preprocessing      : 0
% 0.79/0.94  # Initial clauses in saturation        : 87
% 0.79/0.94  # Processed clauses                    : 5957
% 0.79/0.94  # ...of these trivial                  : 234
% 0.79/0.94  # ...subsumed                          : 2989
% 0.79/0.94  # ...remaining for further processing  : 2734
% 0.79/0.94  # Other redundant clauses eliminated   : 2
% 0.79/0.94  # Clauses deleted for lack of memory   : 0
% 0.79/0.94  # Backward-subsumed                    : 71
% 0.79/0.94  # Backward-rewritten                   : 335
% 0.79/0.94  # Generated clauses                    : 31890
% 0.79/0.94  # ...of the previous two non-trivial   : 29365
% 0.79/0.94  # Contextual simplify-reflections      : 92
% 0.79/0.94  # Paramodulations                      : 31876
% 0.79/0.94  # Factorizations                       : 0
% 0.79/0.94  # Equation resolutions                 : 2
% 0.79/0.94  # Propositional unsat checks           : 0
% 0.79/0.94  #    Propositional check models        : 0
% 0.79/0.94  #    Propositional check unsatisfiable : 0
% 0.79/0.94  #    Propositional clauses             : 0
% 0.79/0.94  #    Propositional clauses after purity: 0
% 0.79/0.94  #    Propositional unsat core size     : 0
% 0.79/0.94  #    Propositional preprocessing time  : 0.000
% 0.79/0.94  #    Propositional encoding time       : 0.000
% 0.79/0.94  #    Propositional solver time         : 0.000
% 0.79/0.94  #    Success case prop preproc time    : 0.000
% 0.79/0.94  #    Success case prop encoding time   : 0.000
% 0.79/0.94  #    Success case prop solver time     : 0.000
% 0.79/0.94  # Current number of processed clauses  : 2252
% 0.79/0.94  #    Positive orientable unit clauses  : 394
% 0.79/0.94  #    Positive unorientable unit clauses: 0
% 0.79/0.94  #    Negative unit clauses             : 10
% 0.79/0.94  #    Non-unit-clauses                  : 1848
% 0.79/0.94  # Current number of unprocessed clauses: 23421
% 0.79/0.94  # ...number of literals in the above   : 100027
% 0.79/0.94  # Current number of archived formulas  : 0
% 0.79/0.94  # Current number of archived clauses   : 480
% 0.79/0.94  # Clause-clause subsumption calls (NU) : 783579
% 0.79/0.94  # Rec. Clause-clause subsumption calls : 324824
% 0.79/0.94  # Non-unit clause-clause subsumptions  : 3125
% 0.79/0.94  # Unit Clause-clause subsumption calls : 159803
% 0.79/0.94  # Rewrite failures with RHS unbound    : 0
% 0.79/0.94  # BW rewrite match attempts            : 2477
% 0.79/0.94  # BW rewrite match successes           : 35
% 0.79/0.94  # Condensation attempts                : 0
% 0.79/0.94  # Condensation successes               : 0
% 0.79/0.94  # Termbank termtop insertions          : 1062222
% 0.79/0.95  
% 0.79/0.95  # -------------------------------------------------
% 0.79/0.95  # User time                : 0.592 s
% 0.79/0.95  # System time              : 0.016 s
% 0.79/0.95  # Total time               : 0.608 s
% 0.79/0.95  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
