%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:32 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  107 (3839 expanded)
%              Number of clauses        :   78 (1243 expanded)
%              Number of leaves         :   13 ( 941 expanded)
%              Depth                    :   19
%              Number of atoms          :  695 (109150 expanded)
%              Number of equality atoms :   18 (2311 expanded)
%              Maximal formula depth    :   49 (   6 average)
%              Maximal clause size      :   91 (   3 average)
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

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X30,X31,X32,X33] :
      ( ( v1_funct_1(k2_tmap_1(X30,X31,X32,X33))
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ l1_struct_0(X33) )
      & ( v1_funct_2(k2_tmap_1(X30,X31,X32,X33),u1_struct_0(X33),u1_struct_0(X31))
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ l1_struct_0(X33) )
      & ( m1_subset_1(k2_tmap_1(X30,X31,X32,X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X31)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))
        | ~ l1_struct_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_14,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

cnf(c_0_15,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | l1_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_26,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ v1_funct_1(X18)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k2_partfun1(X16,X17,X18,X19) = k7_relat_1(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_27,plain,(
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

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_24])])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_32,plain,(
    ! [X23,X24,X25,X26] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ v1_funct_1(X25)
      | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
      | ~ m1_pre_topc(X26,X23)
      | k2_tmap_1(X23,X24,X25,X26) = k2_partfun1(u1_struct_0(X23),u1_struct_0(X24),X25,u1_struct_0(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_33,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_34,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r1_tarski(k1_relat_1(X9),X8)
      | k7_relat_1(X9,X8) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_35,plain,(
    ! [X6,X7] :
      ( ( ~ v4_relat_1(X7,X6)
        | r1_tarski(k1_relat_1(X7),X6)
        | ~ v1_relat_1(X7) )
      & ( ~ r1_tarski(k1_relat_1(X7),X6)
        | v4_relat_1(X7,X6)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_36,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_37,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v2_struct_0(k1_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( v1_pre_topc(k1_tsep_1(X27,X28,X29))
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) )
      & ( m1_pre_topc(k1_tsep_1(X27,X28,X29),X27)
        | v2_struct_0(X27)
        | ~ l1_pre_topc(X27)
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X27)
        | v2_struct_0(X29)
        | ~ m1_pre_topc(X29,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_38,axiom,(
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
    inference(apply_def,[status(thm)],[t129_tmap_1,c_0_27])).

cnf(c_0_39,negated_conjecture,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24])])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_31]),c_0_24])])).

fof(c_0_43,plain,(
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
    inference(split_equiv,[status(thm)],[c_0_27])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_18])])).

cnf(c_0_50,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_52,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_53,plain,(
    ! [X13,X14,X15] :
      ( ( v4_relat_1(X15,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v5_relat_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_54,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_56,plain,(
    ! [X34,X35,X36,X37,X38] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ m1_pre_topc(X36,X34)
      | v2_struct_0(X37)
      | ~ m1_pre_topc(X37,X34)
      | ~ r4_tsep_1(X34,X36,X37)
      | ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,u1_struct_0(X34),u1_struct_0(X35))
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))
      | epred1_5(X35,X36,X37,X38,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_18]),c_0_17]),c_0_16])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

cnf(c_0_60,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_61,plain,(
    ! [X44,X45,X46,X47,X48] :
      ( ( v1_funct_1(k2_tmap_1(X44,X48,X45,X47))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_1(k2_tmap_1(X44,X48,X45,X46))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,X47))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,X46))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,X47))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,X46))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,X47))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,X46))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) )
      & ( m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,X47))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | ~ v1_funct_1(k2_tmap_1(X44,X48,X45,X46))
        | ~ v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))
        | ~ v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)
        | ~ m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))
        | ~ epred1_5(X48,X47,X46,X45,X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).

cnf(c_0_62,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_17]),c_0_45]),c_0_46]),c_0_22]),c_0_24]),c_0_18])]),c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_63,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_16])).

cnf(c_0_65,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_30]),c_0_24])]),c_0_55]),c_0_48])).

cnf(c_0_67,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])]),c_0_59])])).

cnf(c_0_71,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_73,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X5,X4,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,X1) = esk3_0
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ v4_relat_1(esk3_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_75,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_16])).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_31]),c_0_67]),c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( epred1_5(esk2_0,X1,X2,esk3_0,esk1_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r4_tsep_1(esk1_0,X1,X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_16]),c_0_17]),c_0_45]),c_0_46]),c_0_22]),c_0_24]),c_0_18])]),c_0_47]),c_0_48])).

cnf(c_0_78,negated_conjecture,
    ( r4_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_79,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_17]),c_0_18]),c_0_16])]),c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_82,negated_conjecture,
    ( epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_30]),c_0_31])]),c_0_68]),c_0_55])).

cnf(c_0_83,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_84,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))
    | ~ epred1_5(X2,X4,X5,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_85,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_71]),c_0_17]),c_0_18]),c_0_16])]),c_0_72])).

cnf(c_0_86,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_17]),c_0_18]),c_0_16])]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)
    | ~ epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)
    | ~ v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1)))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_67])).

cnf(c_0_88,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_89,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_86])])).

cnf(c_0_90,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_81]),c_0_82]),c_0_17]),c_0_18]),c_0_16])]),c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_21]),c_0_41])])).

cnf(c_0_93,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_21]),c_0_42])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_21]),c_0_24])])).

cnf(c_0_95,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_97,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_21]),c_0_22])])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_99,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_101,negated_conjecture,
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
    inference(spm,[status(thm)],[c_0_95,c_0_67])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_98,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_99,c_0_97])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[c_0_100,c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_81]),c_0_82]),c_0_86]),c_0_90]),c_0_103]),c_0_104]),c_0_58]),c_0_59]),c_0_105])]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.33/2.54  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.33/2.54  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.33/2.54  #
% 2.33/2.54  # Preprocessing time       : 0.031 s
% 2.33/2.54  # Presaturation interreduction done
% 2.33/2.54  
% 2.33/2.54  # Proof found!
% 2.33/2.54  # SZS status Theorem
% 2.33/2.54  # SZS output start CNFRefutation
% 2.33/2.54  fof(t132_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((X1=k1_tsep_1(X1,X4,X5)&r4_tsep_1(X1,X4,X5))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_tmap_1)).
% 2.33/2.54  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 2.33/2.54  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.33/2.54  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.33/2.54  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.33/2.54  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.33/2.54  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.33/2.54  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.33/2.54  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.33/2.54  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 2.33/2.54  fof(t129_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_tmap_1)).
% 2.33/2.54  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.33/2.54  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((X1=k1_tsep_1(X1,X4,X5)&r4_tsep_1(X1,X4,X5))=>((((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&v5_pre_topc(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X3,X5)))&v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2))&m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))))))))))), inference(assume_negation,[status(cth)],[t132_tmap_1])).
% 2.33/2.54  fof(c_0_13, plain, ![X30, X31, X32, X33]:(((v1_funct_1(k2_tmap_1(X30,X31,X32,X33))|(~l1_struct_0(X30)|~l1_struct_0(X31)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))|~l1_struct_0(X33)))&(v1_funct_2(k2_tmap_1(X30,X31,X32,X33),u1_struct_0(X33),u1_struct_0(X31))|(~l1_struct_0(X30)|~l1_struct_0(X31)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))|~l1_struct_0(X33))))&(m1_subset_1(k2_tmap_1(X30,X31,X32,X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))|(~l1_struct_0(X30)|~l1_struct_0(X31)|~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X30),u1_struct_0(X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X31))))|~l1_struct_0(X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 2.33/2.54  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&r4_tsep_1(esk1_0,esk4_0,esk5_0))&((~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|(~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))))&(((((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_1(esk3_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_1(esk3_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_1(esk3_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_1(esk3_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_1(esk3_0)))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0))))&((((((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))))&(m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).
% 2.33/2.54  cnf(c_0_15, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.33/2.54  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  fof(c_0_19, plain, ![X20]:(~l1_pre_topc(X20)|l1_struct_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 2.33/2.54  cnf(c_0_20, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 2.33/2.54  cnf(c_0_21, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.33/2.54  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_23, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 2.33/2.54  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  fof(c_0_25, plain, ![X21, X22]:(~l1_pre_topc(X21)|(~m1_pre_topc(X22,X21)|l1_pre_topc(X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 2.33/2.54  fof(c_0_26, plain, ![X16, X17, X18, X19]:(~v1_funct_1(X18)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k2_partfun1(X16,X17,X18,X19)=k7_relat_1(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 2.33/2.54  fof(c_0_27, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)<=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), introduced(definition)).
% 2.33/2.54  cnf(c_0_28, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_21]), c_0_24])])).
% 2.33/2.54  cnf(c_0_29, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 2.33/2.54  cnf(c_0_30, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  fof(c_0_32, plain, ![X23, X24, X25, X26]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))|(~m1_pre_topc(X26,X23)|k2_tmap_1(X23,X24,X25,X26)=k2_partfun1(u1_struct_0(X23),u1_struct_0(X24),X25,u1_struct_0(X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 2.33/2.54  cnf(c_0_33, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 2.33/2.54  fof(c_0_34, plain, ![X8, X9]:(~v1_relat_1(X9)|(~r1_tarski(k1_relat_1(X9),X8)|k7_relat_1(X9,X8)=X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 2.33/2.54  fof(c_0_35, plain, ![X6, X7]:((~v4_relat_1(X7,X6)|r1_tarski(k1_relat_1(X7),X6)|~v1_relat_1(X7))&(~r1_tarski(k1_relat_1(X7),X6)|v4_relat_1(X7,X6)|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 2.33/2.54  fof(c_0_36, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 2.33/2.54  fof(c_0_37, plain, ![X27, X28, X29]:(((~v2_struct_0(k1_tsep_1(X27,X28,X29))|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27)))&(v1_pre_topc(k1_tsep_1(X27,X28,X29))|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27))))&(m1_pre_topc(k1_tsep_1(X27,X28,X29),X27)|(v2_struct_0(X27)|~l1_pre_topc(X27)|v2_struct_0(X28)|~m1_pre_topc(X28,X27)|v2_struct_0(X29)|~m1_pre_topc(X29,X27)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 2.33/2.54  fof(c_0_38, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(r4_tsep_1(X1,X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>epred1_5(X2,X3,X4,X5,X1))))))), inference(apply_def,[status(thm)],[t129_tmap_1, c_0_27])).
% 2.33/2.54  cnf(c_0_39, negated_conjecture, (~v1_funct_1(esk3_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_40, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_28, c_0_21])).
% 2.33/2.54  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_24])])).
% 2.33/2.54  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_31]), c_0_24])])).
% 2.33/2.54  fof(c_0_43, plain, ![X1, X5, X4, X3, X2]:(epred1_5(X2,X3,X4,X5,X1)=>((((v1_funct_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_tsep_1(X1,X3,X4),X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,k1_tsep_1(X1,X3,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))<=>(((((((v1_funct_1(k2_tmap_1(X1,X2,X5,X3))&v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X3),X3,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))&v1_funct_1(k2_tmap_1(X1,X2,X5,X4)))&v1_funct_2(k2_tmap_1(X1,X2,X5,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X5,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))))), inference(split_equiv,[status(thm)],[c_0_27])).
% 2.33/2.54  cnf(c_0_44, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.33/2.54  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_48, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_16]), c_0_18])])).
% 2.33/2.54  cnf(c_0_50, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 2.33/2.54  cnf(c_0_51, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 2.33/2.54  cnf(c_0_52, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 2.33/2.54  fof(c_0_53, plain, ![X13, X14, X15]:((v4_relat_1(X15,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))&(v5_relat_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 2.33/2.54  cnf(c_0_54, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.33/2.54  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  fof(c_0_56, plain, ![X34, X35, X36, X37, X38]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(v2_struct_0(X36)|~m1_pre_topc(X36,X34)|(v2_struct_0(X37)|~m1_pre_topc(X37,X34)|(~r4_tsep_1(X34,X36,X37)|(~v1_funct_1(X38)|~v1_funct_2(X38,u1_struct_0(X34),u1_struct_0(X35))|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),u1_struct_0(X35))))|epred1_5(X35,X36,X37,X38,X34))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_38])])])])).
% 2.33/2.54  cnf(c_0_57, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_18]), c_0_17]), c_0_16])])).
% 2.33/2.54  cnf(c_0_58, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 2.33/2.54  cnf(c_0_59, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 2.33/2.54  cnf(c_0_60, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.33/2.54  fof(c_0_61, plain, ![X44, X45, X46, X47, X48]:(((((((((v1_funct_1(k2_tmap_1(X44,X48,X45,X47))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|~v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44))&(v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|~v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)|(~v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|~v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|~v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v1_funct_1(k2_tmap_1(X44,X48,X45,X46))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|~v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|~v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)|(~v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|~v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48))))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|~v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&((((v1_funct_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,X47))|~v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~v1_funct_1(k2_tmap_1(X44,X48,X45,X46))|~v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44))&(v1_funct_2(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,X47))|~v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~v1_funct_1(k2_tmap_1(X44,X48,X45,X46))|~v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(v5_pre_topc(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_tsep_1(X44,X47,X46),X48)|(~v1_funct_1(k2_tmap_1(X44,X48,X45,X47))|~v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~v1_funct_1(k2_tmap_1(X44,X48,X45,X46))|~v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))&(m1_subset_1(k2_tmap_1(X44,X48,X45,k1_tsep_1(X44,X47,X46)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X44,X47,X46)),u1_struct_0(X48))))|(~v1_funct_1(k2_tmap_1(X44,X48,X45,X47))|~v1_funct_2(k2_tmap_1(X44,X48,X45,X47),u1_struct_0(X47),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,X47),X47,X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))|~v1_funct_1(k2_tmap_1(X44,X48,X45,X46))|~v1_funct_2(k2_tmap_1(X44,X48,X45,X46),u1_struct_0(X46),u1_struct_0(X48))|~v5_pre_topc(k2_tmap_1(X44,X48,X45,X46),X46,X48)|~m1_subset_1(k2_tmap_1(X44,X48,X45,X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X48)))))|~epred1_5(X48,X47,X46,X45,X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_43])])])).
% 2.33/2.54  cnf(c_0_62, negated_conjecture, (k7_relat_1(esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_16]), c_0_17]), c_0_45]), c_0_46]), c_0_22]), c_0_24]), c_0_18])]), c_0_47]), c_0_48]), c_0_49])).
% 2.33/2.54  cnf(c_0_63, plain, (k7_relat_1(X1,X2)=X1|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 2.33/2.54  cnf(c_0_64, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_52, c_0_16])).
% 2.33/2.54  cnf(c_0_65, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 2.33/2.54  cnf(c_0_66, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_30]), c_0_24])]), c_0_55]), c_0_48])).
% 2.33/2.54  cnf(c_0_67, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_69, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|epred1_5(X2,X3,X4,X5,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~r4_tsep_1(X1,X3,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 2.33/2.54  cnf(c_0_70, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])]), c_0_59])])).
% 2.33/2.54  cnf(c_0_71, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.33/2.54  cnf(c_0_72, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),u1_struct_0(X1),u1_struct_0(esk2_0))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_16]), c_0_17]), c_0_18])])).
% 2.33/2.54  cnf(c_0_73, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_tsep_1(X1,X5,X4),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X5,X4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X5,X4)),u1_struct_0(X2))))|~epred1_5(X2,X5,X4,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.33/2.54  cnf(c_0_74, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)=esk3_0|~m1_pre_topc(X1,esk1_0)|~v4_relat_1(esk3_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 2.33/2.54  cnf(c_0_75, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_65, c_0_16])).
% 2.33/2.54  cnf(c_0_76, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_31]), c_0_67]), c_0_68])).
% 2.33/2.54  cnf(c_0_77, negated_conjecture, (epred1_5(esk2_0,X1,X2,esk3_0,esk1_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r4_tsep_1(esk1_0,X1,X2)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_16]), c_0_17]), c_0_45]), c_0_46]), c_0_22]), c_0_24]), c_0_18])]), c_0_47]), c_0_48])).
% 2.33/2.54  cnf(c_0_78, negated_conjecture, (r4_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_79, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~l1_struct_0(esk5_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_17]), c_0_18]), c_0_16])]), c_0_72])).
% 2.33/2.54  cnf(c_0_80, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_73, c_0_67])).
% 2.33/2.54  cnf(c_0_81, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 2.33/2.54  cnf(c_0_82, negated_conjecture, (epred1_5(esk2_0,esk4_0,esk5_0,esk3_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_30]), c_0_31])]), c_0_68]), c_0_55])).
% 2.33/2.54  cnf(c_0_83, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_84, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)))|~v1_funct_2(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X4,X5)),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.33/2.54  cnf(c_0_85, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_71]), c_0_17]), c_0_18]), c_0_16])]), c_0_72])).
% 2.33/2.54  cnf(c_0_86, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk5_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_17]), c_0_18]), c_0_16])]), c_0_83])).
% 2.33/2.54  cnf(c_0_87, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk1_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk1_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_84, c_0_67])).
% 2.33/2.54  cnf(c_0_88, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_89, negated_conjecture, (~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_86])])).
% 2.33/2.54  cnf(c_0_90, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk4_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_81]), c_0_82]), c_0_17]), c_0_18]), c_0_16])]), c_0_88])).
% 2.33/2.54  cnf(c_0_91, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 2.33/2.54  cnf(c_0_92, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_21]), c_0_41])])).
% 2.33/2.54  cnf(c_0_93, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_21]), c_0_42])])).
% 2.33/2.54  cnf(c_0_94, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_21]), c_0_24])])).
% 2.33/2.54  cnf(c_0_95, plain, (v5_pre_topc(k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),k1_tsep_1(X1,X4,X5),X2)|~v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(k2_tmap_1(X1,X2,X3,X5))|~v1_funct_2(k2_tmap_1(X1,X2,X3,X5),u1_struct_0(X5),u1_struct_0(X2))|~v5_pre_topc(k2_tmap_1(X1,X2,X3,X5),X5,X2)|~m1_subset_1(k2_tmap_1(X1,X2,X3,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))|~epred1_5(X2,X4,X5,X3,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 2.33/2.54  cnf(c_0_96, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_97, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_21]), c_0_22])])).
% 2.33/2.54  cnf(c_0_98, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_99, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_100, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 2.33/2.54  cnf(c_0_101, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk1_0),esk1_0,X1)|~epred1_5(X1,esk4_0,esk5_0,X2,esk1_0)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk5_0),esk5_0,X1)|~v5_pre_topc(k2_tmap_1(esk1_0,X1,X2,esk4_0),esk4_0,X1)|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk5_0),u1_struct_0(esk5_0),u1_struct_0(X1))|~v1_funct_2(k2_tmap_1(esk1_0,X1,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk5_0))|~v1_funct_1(k2_tmap_1(esk1_0,X1,X2,esk4_0))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(X1))))|~m1_subset_1(k2_tmap_1(esk1_0,X1,X2,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))), inference(spm,[status(thm)],[c_0_95, c_0_67])).
% 2.33/2.54  cnf(c_0_102, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[c_0_96, c_0_97])).
% 2.33/2.54  cnf(c_0_103, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_98, c_0_97])).
% 2.33/2.54  cnf(c_0_104, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[c_0_99, c_0_97])).
% 2.33/2.54  cnf(c_0_105, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[c_0_100, c_0_97])).
% 2.33/2.54  cnf(c_0_106, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_81]), c_0_82]), c_0_86]), c_0_90]), c_0_103]), c_0_104]), c_0_58]), c_0_59]), c_0_105])]), c_0_97]), ['proof']).
% 2.33/2.54  # SZS output end CNFRefutation
% 2.33/2.54  # Proof object total steps             : 107
% 2.33/2.54  # Proof object clause steps            : 78
% 2.33/2.54  # Proof object formula steps           : 29
% 2.33/2.54  # Proof object conjectures             : 64
% 2.33/2.54  # Proof object clause conjectures      : 61
% 2.33/2.54  # Proof object formula conjectures     : 3
% 2.33/2.54  # Proof object initial clauses used    : 38
% 2.33/2.54  # Proof object initial formulas used   : 12
% 2.33/2.54  # Proof object generating inferences   : 32
% 2.33/2.54  # Proof object simplifying inferences  : 107
% 2.33/2.54  # Training examples: 0 positive, 0 negative
% 2.33/2.54  # Parsed axioms                        : 12
% 2.33/2.54  # Removed by relevancy pruning/SinE    : 0
% 2.33/2.54  # Initial clauses                      : 77
% 2.33/2.54  # Removed in clause preprocessing      : 0
% 2.33/2.54  # Initial clauses in saturation        : 77
% 2.33/2.54  # Processed clauses                    : 3900
% 2.33/2.54  # ...of these trivial                  : 26
% 2.33/2.54  # ...subsumed                          : 50
% 2.33/2.54  # ...remaining for further processing  : 3824
% 2.33/2.54  # Other redundant clauses eliminated   : 0
% 2.33/2.54  # Clauses deleted for lack of memory   : 0
% 2.33/2.54  # Backward-subsumed                    : 63
% 2.33/2.54  # Backward-rewritten                   : 18
% 2.33/2.54  # Generated clauses                    : 141374
% 2.33/2.54  # ...of the previous two non-trivial   : 141292
% 2.33/2.54  # Contextual simplify-reflections      : 63
% 2.33/2.54  # Paramodulations                      : 141218
% 2.33/2.54  # Factorizations                       : 0
% 2.33/2.54  # Equation resolutions                 : 0
% 2.33/2.54  # Propositional unsat checks           : 0
% 2.33/2.54  #    Propositional check models        : 0
% 2.33/2.54  #    Propositional check unsatisfiable : 0
% 2.33/2.54  #    Propositional clauses             : 0
% 2.33/2.54  #    Propositional clauses after purity: 0
% 2.33/2.54  #    Propositional unsat core size     : 0
% 2.33/2.54  #    Propositional preprocessing time  : 0.000
% 2.33/2.54  #    Propositional encoding time       : 0.000
% 2.33/2.54  #    Propositional solver time         : 0.000
% 2.33/2.54  #    Success case prop preproc time    : 0.000
% 2.33/2.54  #    Success case prop encoding time   : 0.000
% 2.33/2.54  #    Success case prop solver time     : 0.000
% 2.33/2.54  # Current number of processed clauses  : 3534
% 2.33/2.54  #    Positive orientable unit clauses  : 139
% 2.33/2.54  #    Positive unorientable unit clauses: 0
% 2.33/2.54  #    Negative unit clauses             : 5
% 2.33/2.54  #    Non-unit-clauses                  : 3390
% 2.33/2.54  # Current number of unprocessed clauses: 137508
% 2.33/2.54  # ...number of literals in the above   : 815222
% 2.33/2.54  # Current number of archived formulas  : 0
% 2.33/2.54  # Current number of archived clauses   : 290
% 2.33/2.54  # Clause-clause subsumption calls (NU) : 6832615
% 2.33/2.54  # Rec. Clause-clause subsumption calls : 939691
% 2.33/2.54  # Non-unit clause-clause subsumptions  : 171
% 2.33/2.54  # Unit Clause-clause subsumption calls : 1531
% 2.33/2.54  # Rewrite failures with RHS unbound    : 0
% 2.33/2.54  # BW rewrite match attempts            : 725
% 2.33/2.54  # BW rewrite match successes           : 9
% 2.33/2.54  # Condensation attempts                : 0
% 2.33/2.54  # Condensation successes               : 0
% 2.33/2.54  # Termbank termtop insertions          : 7708427
% 2.33/2.55  
% 2.33/2.55  # -------------------------------------------------
% 2.33/2.55  # User time                : 2.123 s
% 2.33/2.55  # System time              : 0.085 s
% 2.33/2.55  # Total time               : 2.208 s
% 2.33/2.55  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
