%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:25 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.71s
% Verified   : 
% Statistics : Number of formulae       :  215 (2362 expanded)
%              Number of clauses        :  136 ( 497 expanded)
%              Number of leaves         :   16 (1028 expanded)
%              Depth                    :   21
%              Number of atoms          : 2294 (54196 expanded)
%              Number of equality atoms :  445 (1127 expanded)
%              Maximal formula depth    :   26 (  11 average)
%              Maximal clause size      :   50 (   9 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(X5,X3,X1)
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r4_tsep_1(X0,X2,X3)
                                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(X4,X2,X1)
                            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                                & v5_pre_topc(X5,X3,X1)
                                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                                & v1_funct_1(X5) )
                             => ( ( r4_tsep_1(X0,X2,X3)
                                  & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
          & r4_tsep_1(X0,X2,X3)
          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(X5,X3,X1)
          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(X5) )
     => ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7)) )
        & r4_tsep_1(X0,X2,X3)
        & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),sK7))
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(sK7,X3,X1)
        & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
              & r4_tsep_1(X0,X2,X3)
              & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
              & v5_pre_topc(X5,X3,X1)
              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(X4,X2,X1)
          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_tsep_1(X0,X2,X3),X1)
              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5)) )
            & r4_tsep_1(X0,X2,X3)
            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),sK6),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
            & v5_pre_topc(X5,X3,X1)
            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(sK6,X2,X1)
        & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                    | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                    | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                    | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                  & r4_tsep_1(X0,X2,X3)
                  & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                  & v5_pre_topc(X5,X3,X1)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
              & v5_pre_topc(X4,X2,X1)
              & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & ~ r1_tsep_1(X2,X3)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))))
                  | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1)
                  | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1))
                  | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5)) )
                & r4_tsep_1(X0,X2,sK5)
                & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,sK5),X4),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,X2,sK5),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
                & v5_pre_topc(X5,sK5,X1)
                & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
            & v5_pre_topc(X4,X2,X1)
            & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & ~ r1_tsep_1(X2,sK5)
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                        | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                      & r4_tsep_1(X0,X2,X3)
                      & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v5_pre_topc(X5,X3,X1)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v5_pre_topc(X4,X2,X1)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & ~ r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_tsep_1(X0,sK4,X3),X1)
                      | ~ v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5)) )
                    & r4_tsep_1(X0,sK4,X3)
                    & r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,sK4,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v5_pre_topc(X5,X3,X1)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
                & v5_pre_topc(X4,sK4,X1)
                & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & ~ r1_tsep_1(sK4,X3)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(X0,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))))
                          | ~ v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),sK3)
                          | ~ v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3))
                          | ~ v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5)) )
                        & r4_tsep_1(X0,X2,X3)
                        & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,sK3,X3,k2_tsep_1(X0,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                        & v5_pre_topc(X5,X3,sK3)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
                    & v5_pre_topc(X4,X2,sK3)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3))
                    & v1_funct_1(X4) )
                & ~ r1_tsep_1(X2,X3)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK3)
        & v2_pre_topc(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ~ m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                              | ~ v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                              | ~ v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                              | ~ v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                            & r4_tsep_1(X0,X2,X3)
                            & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(X5,X3,X1)
                            & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & ~ r1_tsep_1(X2,X3)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ~ m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5)) )
                          & r4_tsep_1(sK2,X2,X3)
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) )
    & r4_tsep_1(sK2,sK4,sK5)
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v5_pre_topc(sK7,sK5,sK3)
    & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    & v5_pre_topc(sK6,sK4,sK3)
    & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & ~ r1_tsep_1(sK4,sK5)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f27,f45,f44,f43,f42,f41,f40])).

fof(f95,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(X5) )
                           => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                          <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                                & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) )
                              | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) )
                            & ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                              | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
                              | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | r1_tsep_1(X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
    ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f77,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( sP0(X1,X3,X4,X2,X0)
    <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( sP0(X1,X3,X4,X2,X0)
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
        | ~ m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
        | ~ v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
      & ( ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) )
        | ~ sP0(X1,X3,X4,X2,X0) ) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
        | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
        | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
        | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
        | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
      & ( ( m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
          & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
          & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
          & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
          & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f36])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4)
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f29,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(X4) )
      <=> sP0(X1,X3,X4,X2,X0) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f32,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f33,plain,(
    ! [X0,X2,X4,X3,X1] :
      ( ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(X4) )
          | ~ sP0(X1,X3,X4,X2,X0) )
        & ( sP0(X1,X3,X4,X2,X0)
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(X4) ) )
      | ~ sP1(X0,X2,X4,X3,X1) ) ),
    inference(flattening,[],[f32])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
            & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
            & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
            & v1_funct_1(X2) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
          | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(X2) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f33])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                        <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                            & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                      <=> ( m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))
                          & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X0,X2,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f18,f29,f28])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP1(X0,X2,X4,X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,(
    r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f97,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_31,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1527,negated_conjecture,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2278,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1527])).

cnf(c_23,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | r1_tsep_1(X3,X0)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_40,negated_conjecture,
    ( ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_723,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | sK5 != X0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_40])).

cnf(c_724,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_44,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_728,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_44,c_42])).

cnf(c_729,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(renaming,[status(thm)],[c_728])).

cnf(c_1507,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,sK4,k2_tsep_1(X0_55,sK4,sK5),X0_54),k3_tmap_1(X0_55,X1_55,sK5,k2_tsep_1(X0_55,sK4,sK5),X1_54))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54)),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55))
    | ~ m1_pre_topc(sK5,X0_55)
    | ~ m1_pre_topc(sK4,X0_55)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_729])).

cnf(c_2298,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,sK4,k2_tsep_1(X0_55,sK4,sK5),X0_54),k3_tmap_1(X0_55,X1_55,sK5,k2_tsep_1(X0_55,sK4,sK5),X1_54)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54)),X1_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1507])).

cnf(c_6503,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2298])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_51,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_49,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_52,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_53,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_47,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_54,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_55,plain,
    ( v2_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_56,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_43,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_58,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_41,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_60,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_62,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_63,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_65,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_66,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_67,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_69,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_70,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2950,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,X0_55,sK5,k2_tsep_1(sK2,sK4,sK5),X1_54))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,X0_55,sK4,sK5,X0_54,X1_54)),X1_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(instantiation,[status(thm)],[c_1507])).

cnf(c_3318,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),sK7)
    | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2950])).

cnf(c_3319,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),sK7) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3318])).

cnf(c_3321,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3319])).

cnf(c_6506,plain,
    ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6503,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_60,c_62,c_63,c_65,c_66,c_67,c_69,c_70,c_3321])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1534,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2271,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1534])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1538,plain,
    ( ~ r2_funct_2(X0_56,X1_56,X0_54,X1_54)
    | ~ v1_funct_2(X1_54,X0_56,X1_56)
    | ~ v1_funct_2(X0_54,X0_56,X1_56)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | X0_54 = X1_54 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2267,plain,
    ( X0_54 = X1_54
    | r2_funct_2(X0_56,X1_56,X0_54,X1_54) != iProver_top
    | v1_funct_2(X0_54,X0_56,X1_56) != iProver_top
    | v1_funct_2(X1_54,X0_56,X1_56) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1538])).

cnf(c_4669,plain,
    ( k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54) = X1_54
    | r2_funct_2(u1_struct_0(X3_55),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54),X1_54) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X3_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54),u1_struct_0(X3_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X3_55,X0_55) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_2267])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1532,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X3_55)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2273,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X3_55) != iProver_top
    | m1_pre_topc(X0_55,X3_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X3_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X3_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X3_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1532])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1533,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_54),u1_struct_0(X3_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X3_55,X2_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X2_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X2_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2272,plain,
    ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_54),u1_struct_0(X3_55),u1_struct_0(X1_55)) = iProver_top
    | m1_pre_topc(X3_55,X2_55) != iProver_top
    | m1_pre_topc(X0_55,X2_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X2_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X2_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X2_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_9465,plain,
    ( k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54) = X1_54
    | r2_funct_2(u1_struct_0(X3_55),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54),X1_54) != iProver_top
    | v1_funct_2(X1_54,u1_struct_0(X3_55),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(X2_55,X0_55) != iProver_top
    | m1_pre_topc(X3_55,X0_55) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4669,c_2273,c_2272])).

cnf(c_9471,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6506,c_9465])).

cnf(c_57,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_59,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_27,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1530,plain,
    ( m1_pre_topc(X0_55,X0_55)
    | ~ l1_pre_topc(X0_55) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_3700,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1530])).

cnf(c_3703,plain,
    ( m1_pre_topc(sK2,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3700])).

cnf(c_4,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1535,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3059,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_54,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_3261,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k10_tmap_1(sK2,sK3,X0_55,sK5,X0_54,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3059])).

cnf(c_3808,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3261])).

cnf(c_3809,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3808])).

cnf(c_3811,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3809])).

cnf(c_3,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1536,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3069,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_3281,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(sK2,sK3,X0_55,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,X0_55,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3069])).

cnf(c_3838,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3281])).

cnf(c_3839,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3838])).

cnf(c_3841,plain,
    ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3839])).

cnf(c_2,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1537,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
    | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
    | ~ m1_pre_topc(X2_55,X3_55)
    | ~ m1_pre_topc(X0_55,X3_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
    | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X3_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X3_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3086,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1537])).

cnf(c_3297,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(sK2,sK3,X0_55,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_55,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3086])).

cnf(c_3946,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3297])).

cnf(c_3947,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3946])).

cnf(c_3949,plain,
    ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3947])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X0,X2)
    | m1_pre_topc(k1_tsep_1(X1,X3,X0),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1531,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X1_55)
    | ~ m1_pre_topc(X3_55,X2_55)
    | ~ m1_pre_topc(X3_55,X1_55)
    | ~ m1_pre_topc(X0_55,X2_55)
    | m1_pre_topc(k1_tsep_1(X1_55,X3_55,X0_55),X2_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X3_55)
    | v2_struct_0(X2_55) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_3706,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X2_55,X1_55)
    | ~ m1_pre_topc(X0_55,sK2)
    | ~ m1_pre_topc(X2_55,sK2)
    | m1_pre_topc(k1_tsep_1(X1_55,X2_55,X0_55),sK2)
    | ~ m1_pre_topc(sK2,X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X2_55)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_5393,plain,
    ( ~ m1_pre_topc(X0_55,X1_55)
    | ~ m1_pre_topc(X0_55,sK2)
    | m1_pre_topc(k1_tsep_1(X1_55,X0_55,sK5),sK2)
    | ~ m1_pre_topc(sK5,X1_55)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,X1_55)
    | ~ v2_pre_topc(X1_55)
    | ~ l1_pre_topc(X1_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3706])).

cnf(c_6327,plain,
    ( m1_pre_topc(k1_tsep_1(X0_55,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,X0_55)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,X0_55)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,X0_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5393])).

cnf(c_6666,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6327])).

cnf(c_6667,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6666])).

cnf(c_10731,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9471,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_65,c_66,c_67,c_69,c_3703,c_3811,c_3841,c_3949,c_6667])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,X3,X4)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
    | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
    | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
    | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
    | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9,plain,
    ( ~ sP1(X0,X1,X2,X3,X4)
    | ~ sP0(X4,X3,X2,X1,X0)
    | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ r4_tsep_1(X0,X1,X3)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_30,negated_conjecture,
    ( r4_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_535,plain,
    ( sP1(X0,X1,X2,X3,X4)
    | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X4)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | ~ v1_funct_1(X2)
    | sK5 != X3
    | sK4 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_536,plain,
    ( sP1(sK2,sK4,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_540,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | sP1(sK2,sK4,X0,sK5,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_50,c_49,c_48,c_44,c_43,c_42,c_41])).

cnf(c_541,plain,
    ( sP1(sK2,sK4,X0,sK5,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_540])).

cnf(c_610,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
    | ~ v2_pre_topc(X6)
    | ~ l1_pre_topc(X6)
    | v2_struct_0(X6)
    | ~ v1_funct_1(X5)
    | X5 != X2
    | X6 != X0
    | sK5 != X1
    | sK4 != X3
    | sK2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_541])).

cnf(c_611,plain,
    ( ~ sP0(X0,sK5,X1,sK4,sK2)
    | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
    | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X1) ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_855,plain,
    ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),X5,X3)
    | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),X4,X3)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),u1_struct_0(X5),u1_struct_0(X3))
    | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
    | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6))
    | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
    | X0 != X6
    | X1 != X3
    | sK5 != X5
    | sK4 != X4
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_611])).

cnf(c_856,plain,
    ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),sK5,X1)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),sK4,X1)
    | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0))
    | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
    inference(unflattening,[status(thm)],[c_855])).

cnf(c_1505,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK5,X0_55)
    | ~ v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK4,X0_55)
    | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
    | ~ v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54))
    | ~ v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) ),
    inference(subtyping,[status(esa)],[c_856])).

cnf(c_2300,plain,
    ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK5,X0_55) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK4,X0_55) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1505])).

cnf(c_10742,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
    | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10731,c_2300])).

cnf(c_24,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | r1_tsep_1(X0,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_783,plain,
    ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
    | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | sK5 != X3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_40])).

cnf(c_784,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_788,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_784,c_44,c_42])).

cnf(c_789,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
    | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
    | ~ m1_pre_topc(sK5,X0)
    | ~ m1_pre_topc(sK4,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(renaming,[status(thm)],[c_788])).

cnf(c_1506,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,sK4,k2_tsep_1(X0_55,sK4,sK5),X0_54),k3_tmap_1(X0_55,X1_55,sK5,k2_tsep_1(X0_55,sK4,sK5),X1_54))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54)),X0_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55))
    | ~ m1_pre_topc(sK5,X0_55)
    | ~ m1_pre_topc(sK4,X0_55)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
    | ~ v2_pre_topc(X1_55)
    | ~ v2_pre_topc(X0_55)
    | ~ l1_pre_topc(X1_55)
    | ~ l1_pre_topc(X0_55)
    | v2_struct_0(X1_55)
    | v2_struct_0(X0_55)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_789])).

cnf(c_2299,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,sK4,k2_tsep_1(X0_55,sK4,sK5),X0_54),k3_tmap_1(X0_55,X1_55,sK5,k2_tsep_1(X0_55,sK4,sK5),X1_54)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54)),X0_54) = iProver_top
    | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55)) != iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55)) != iProver_top
    | m1_pre_topc(sK5,X0_55) != iProver_top
    | m1_pre_topc(sK4,X0_55) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55)))) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55)))) != iProver_top
    | v2_pre_topc(X1_55) != iProver_top
    | v2_pre_topc(X0_55) != iProver_top
    | l1_pre_topc(X1_55) != iProver_top
    | l1_pre_topc(X0_55) != iProver_top
    | v2_struct_0(X1_55) = iProver_top
    | v2_struct_0(X0_55) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1506])).

cnf(c_6695,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2278,c_2299])).

cnf(c_2945,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,X0_55,sK5,k2_tsep_1(sK2,sK4,sK5),X1_54))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,X0_55,sK4,sK5,X0_54,X1_54)),X0_54)
    | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55))
    | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X0_55))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
    | ~ v2_pre_topc(X0_55)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(X0_55)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0_55)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_3313,plain,
    ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),X0_54)
    | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2945])).

cnf(c_3314,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),X0_54) = iProver_top
    | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3313])).

cnf(c_3316,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
    | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3314])).

cnf(c_6698,plain,
    ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6695,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_60,c_62,c_63,c_65,c_66,c_67,c_69,c_70,c_3316])).

cnf(c_9470,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6698,c_9465])).

cnf(c_9789,plain,
    ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9470,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,c_60,c_62,c_63,c_65,c_66,c_67,c_69,c_3703,c_3811,c_3841,c_3949,c_6667])).

cnf(c_10841,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
    | v5_pre_topc(sK7,sK5,sK3) != iProver_top
    | v5_pre_topc(sK6,sK4,sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
    | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10742,c_9789,c_10731])).

cnf(c_29,negated_conjecture,
    ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
    | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
    | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
    | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_72,plain,
    ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
    | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_33,negated_conjecture,
    ( v5_pre_topc(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_68,plain,
    ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,negated_conjecture,
    ( v5_pre_topc(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_64,plain,
    ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10841,c_3949,c_3841,c_3811,c_72,c_69,c_68,c_67,c_66,c_65,c_64,c_63,c_62,c_60,c_59,c_58,c_57,c_56,c_55,c_54,c_53,c_52,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:58:15 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 6.71/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.71/1.47  
% 6.71/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.71/1.47  
% 6.71/1.47  ------  iProver source info
% 6.71/1.47  
% 6.71/1.47  git: date: 2020-06-30 10:37:57 +0100
% 6.71/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.71/1.47  git: non_committed_changes: false
% 6.71/1.47  git: last_make_outside_of_git: false
% 6.71/1.47  
% 6.71/1.47  ------ 
% 6.71/1.47  
% 6.71/1.47  ------ Input Options
% 6.71/1.47  
% 6.71/1.47  --out_options                           all
% 6.71/1.47  --tptp_safe_out                         true
% 6.71/1.47  --problem_path                          ""
% 6.71/1.47  --include_path                          ""
% 6.71/1.47  --clausifier                            res/vclausify_rel
% 6.71/1.47  --clausifier_options                    --mode clausify
% 6.71/1.47  --stdin                                 false
% 6.71/1.47  --stats_out                             all
% 6.71/1.47  
% 6.71/1.47  ------ General Options
% 6.71/1.47  
% 6.71/1.47  --fof                                   false
% 6.71/1.47  --time_out_real                         305.
% 6.71/1.47  --time_out_virtual                      -1.
% 6.71/1.47  --symbol_type_check                     false
% 6.71/1.47  --clausify_out                          false
% 6.71/1.47  --sig_cnt_out                           false
% 6.71/1.47  --trig_cnt_out                          false
% 6.71/1.47  --trig_cnt_out_tolerance                1.
% 6.71/1.47  --trig_cnt_out_sk_spl                   false
% 6.71/1.47  --abstr_cl_out                          false
% 6.71/1.47  
% 6.71/1.47  ------ Global Options
% 6.71/1.47  
% 6.71/1.47  --schedule                              default
% 6.71/1.47  --add_important_lit                     false
% 6.71/1.47  --prop_solver_per_cl                    1000
% 6.71/1.47  --min_unsat_core                        false
% 6.71/1.47  --soft_assumptions                      false
% 6.71/1.47  --soft_lemma_size                       3
% 6.71/1.47  --prop_impl_unit_size                   0
% 6.71/1.47  --prop_impl_unit                        []
% 6.71/1.47  --share_sel_clauses                     true
% 6.71/1.47  --reset_solvers                         false
% 6.71/1.47  --bc_imp_inh                            [conj_cone]
% 6.71/1.47  --conj_cone_tolerance                   3.
% 6.71/1.47  --extra_neg_conj                        none
% 6.71/1.47  --large_theory_mode                     true
% 6.71/1.47  --prolific_symb_bound                   200
% 6.71/1.47  --lt_threshold                          2000
% 6.71/1.47  --clause_weak_htbl                      true
% 6.71/1.47  --gc_record_bc_elim                     false
% 6.71/1.47  
% 6.71/1.47  ------ Preprocessing Options
% 6.71/1.47  
% 6.71/1.47  --preprocessing_flag                    true
% 6.71/1.47  --time_out_prep_mult                    0.1
% 6.71/1.47  --splitting_mode                        input
% 6.71/1.47  --splitting_grd                         true
% 6.71/1.47  --splitting_cvd                         false
% 6.71/1.47  --splitting_cvd_svl                     false
% 6.71/1.47  --splitting_nvd                         32
% 6.71/1.47  --sub_typing                            true
% 6.71/1.47  --prep_gs_sim                           true
% 6.71/1.47  --prep_unflatten                        true
% 6.71/1.47  --prep_res_sim                          true
% 6.71/1.47  --prep_upred                            true
% 6.71/1.47  --prep_sem_filter                       exhaustive
% 6.71/1.47  --prep_sem_filter_out                   false
% 6.71/1.47  --pred_elim                             true
% 6.71/1.47  --res_sim_input                         true
% 6.71/1.47  --eq_ax_congr_red                       true
% 6.71/1.47  --pure_diseq_elim                       true
% 6.71/1.47  --brand_transform                       false
% 6.71/1.47  --non_eq_to_eq                          false
% 6.71/1.47  --prep_def_merge                        true
% 6.71/1.47  --prep_def_merge_prop_impl              false
% 6.71/1.47  --prep_def_merge_mbd                    true
% 6.71/1.47  --prep_def_merge_tr_red                 false
% 6.71/1.47  --prep_def_merge_tr_cl                  false
% 6.71/1.47  --smt_preprocessing                     true
% 6.71/1.47  --smt_ac_axioms                         fast
% 6.71/1.47  --preprocessed_out                      false
% 6.71/1.47  --preprocessed_stats                    false
% 6.71/1.47  
% 6.71/1.47  ------ Abstraction refinement Options
% 6.71/1.47  
% 6.71/1.47  --abstr_ref                             []
% 6.71/1.47  --abstr_ref_prep                        false
% 6.71/1.47  --abstr_ref_until_sat                   false
% 6.71/1.47  --abstr_ref_sig_restrict                funpre
% 6.71/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 6.71/1.47  --abstr_ref_under                       []
% 6.71/1.47  
% 6.71/1.47  ------ SAT Options
% 6.71/1.47  
% 6.71/1.47  --sat_mode                              false
% 6.71/1.47  --sat_fm_restart_options                ""
% 6.71/1.47  --sat_gr_def                            false
% 6.71/1.47  --sat_epr_types                         true
% 6.71/1.47  --sat_non_cyclic_types                  false
% 6.71/1.47  --sat_finite_models                     false
% 6.71/1.47  --sat_fm_lemmas                         false
% 6.71/1.47  --sat_fm_prep                           false
% 6.71/1.47  --sat_fm_uc_incr                        true
% 6.71/1.47  --sat_out_model                         small
% 6.71/1.47  --sat_out_clauses                       false
% 6.71/1.47  
% 6.71/1.47  ------ QBF Options
% 6.71/1.47  
% 6.71/1.47  --qbf_mode                              false
% 6.71/1.47  --qbf_elim_univ                         false
% 6.71/1.47  --qbf_dom_inst                          none
% 6.71/1.47  --qbf_dom_pre_inst                      false
% 6.71/1.47  --qbf_sk_in                             false
% 6.71/1.47  --qbf_pred_elim                         true
% 6.71/1.47  --qbf_split                             512
% 6.71/1.47  
% 6.71/1.47  ------ BMC1 Options
% 6.71/1.47  
% 6.71/1.47  --bmc1_incremental                      false
% 6.71/1.47  --bmc1_axioms                           reachable_all
% 6.71/1.47  --bmc1_min_bound                        0
% 6.71/1.47  --bmc1_max_bound                        -1
% 6.71/1.47  --bmc1_max_bound_default                -1
% 6.71/1.47  --bmc1_symbol_reachability              true
% 6.71/1.47  --bmc1_property_lemmas                  false
% 6.71/1.47  --bmc1_k_induction                      false
% 6.71/1.47  --bmc1_non_equiv_states                 false
% 6.71/1.47  --bmc1_deadlock                         false
% 6.71/1.47  --bmc1_ucm                              false
% 6.71/1.47  --bmc1_add_unsat_core                   none
% 6.71/1.47  --bmc1_unsat_core_children              false
% 6.71/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 6.71/1.47  --bmc1_out_stat                         full
% 6.71/1.47  --bmc1_ground_init                      false
% 6.71/1.47  --bmc1_pre_inst_next_state              false
% 6.71/1.47  --bmc1_pre_inst_state                   false
% 6.71/1.47  --bmc1_pre_inst_reach_state             false
% 6.71/1.47  --bmc1_out_unsat_core                   false
% 6.71/1.47  --bmc1_aig_witness_out                  false
% 6.71/1.47  --bmc1_verbose                          false
% 6.71/1.47  --bmc1_dump_clauses_tptp                false
% 6.71/1.47  --bmc1_dump_unsat_core_tptp             false
% 6.71/1.47  --bmc1_dump_file                        -
% 6.71/1.47  --bmc1_ucm_expand_uc_limit              128
% 6.71/1.47  --bmc1_ucm_n_expand_iterations          6
% 6.71/1.47  --bmc1_ucm_extend_mode                  1
% 6.71/1.47  --bmc1_ucm_init_mode                    2
% 6.71/1.47  --bmc1_ucm_cone_mode                    none
% 6.71/1.47  --bmc1_ucm_reduced_relation_type        0
% 6.71/1.47  --bmc1_ucm_relax_model                  4
% 6.71/1.47  --bmc1_ucm_full_tr_after_sat            true
% 6.71/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 6.71/1.47  --bmc1_ucm_layered_model                none
% 6.71/1.47  --bmc1_ucm_max_lemma_size               10
% 6.71/1.47  
% 6.71/1.47  ------ AIG Options
% 6.71/1.47  
% 6.71/1.47  --aig_mode                              false
% 6.71/1.47  
% 6.71/1.47  ------ Instantiation Options
% 6.71/1.47  
% 6.71/1.47  --instantiation_flag                    true
% 6.71/1.47  --inst_sos_flag                         false
% 6.71/1.47  --inst_sos_phase                        true
% 6.71/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.71/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.71/1.47  --inst_lit_sel_side                     num_symb
% 6.71/1.47  --inst_solver_per_active                1400
% 6.71/1.47  --inst_solver_calls_frac                1.
% 6.71/1.47  --inst_passive_queue_type               priority_queues
% 6.71/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.71/1.47  --inst_passive_queues_freq              [25;2]
% 6.71/1.47  --inst_dismatching                      true
% 6.71/1.47  --inst_eager_unprocessed_to_passive     true
% 6.71/1.47  --inst_prop_sim_given                   true
% 6.71/1.47  --inst_prop_sim_new                     false
% 6.71/1.47  --inst_subs_new                         false
% 6.71/1.48  --inst_eq_res_simp                      false
% 6.71/1.48  --inst_subs_given                       false
% 6.71/1.48  --inst_orphan_elimination               true
% 6.71/1.48  --inst_learning_loop_flag               true
% 6.71/1.48  --inst_learning_start                   3000
% 6.71/1.48  --inst_learning_factor                  2
% 6.71/1.48  --inst_start_prop_sim_after_learn       3
% 6.71/1.48  --inst_sel_renew                        solver
% 6.71/1.48  --inst_lit_activity_flag                true
% 6.71/1.48  --inst_restr_to_given                   false
% 6.71/1.48  --inst_activity_threshold               500
% 6.71/1.48  --inst_out_proof                        true
% 6.71/1.48  
% 6.71/1.48  ------ Resolution Options
% 6.71/1.48  
% 6.71/1.48  --resolution_flag                       true
% 6.71/1.48  --res_lit_sel                           adaptive
% 6.71/1.48  --res_lit_sel_side                      none
% 6.71/1.48  --res_ordering                          kbo
% 6.71/1.48  --res_to_prop_solver                    active
% 6.71/1.48  --res_prop_simpl_new                    false
% 6.71/1.48  --res_prop_simpl_given                  true
% 6.71/1.48  --res_passive_queue_type                priority_queues
% 6.71/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.71/1.48  --res_passive_queues_freq               [15;5]
% 6.71/1.48  --res_forward_subs                      full
% 6.71/1.48  --res_backward_subs                     full
% 6.71/1.48  --res_forward_subs_resolution           true
% 6.71/1.48  --res_backward_subs_resolution          true
% 6.71/1.48  --res_orphan_elimination                true
% 6.71/1.48  --res_time_limit                        2.
% 6.71/1.48  --res_out_proof                         true
% 6.71/1.48  
% 6.71/1.48  ------ Superposition Options
% 6.71/1.48  
% 6.71/1.48  --superposition_flag                    true
% 6.71/1.48  --sup_passive_queue_type                priority_queues
% 6.71/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.71/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.71/1.48  --demod_completeness_check              fast
% 6.71/1.48  --demod_use_ground                      true
% 6.71/1.48  --sup_to_prop_solver                    passive
% 6.71/1.48  --sup_prop_simpl_new                    true
% 6.71/1.48  --sup_prop_simpl_given                  true
% 6.71/1.48  --sup_fun_splitting                     false
% 6.71/1.48  --sup_smt_interval                      50000
% 6.71/1.48  
% 6.71/1.48  ------ Superposition Simplification Setup
% 6.71/1.48  
% 6.71/1.48  --sup_indices_passive                   []
% 6.71/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.71/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.71/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.71/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.71/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.71/1.48  --sup_full_bw                           [BwDemod]
% 6.71/1.48  --sup_immed_triv                        [TrivRules]
% 6.71/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.71/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.71/1.48  --sup_immed_bw_main                     []
% 6.71/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.71/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.71/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.71/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.71/1.48  
% 6.71/1.48  ------ Combination Options
% 6.71/1.48  
% 6.71/1.48  --comb_res_mult                         3
% 6.71/1.48  --comb_sup_mult                         2
% 6.71/1.48  --comb_inst_mult                        10
% 6.71/1.48  
% 6.71/1.48  ------ Debug Options
% 6.71/1.48  
% 6.71/1.48  --dbg_backtrace                         false
% 6.71/1.48  --dbg_dump_prop_clauses                 false
% 6.71/1.48  --dbg_dump_prop_clauses_file            -
% 6.71/1.48  --dbg_out_stat                          false
% 6.71/1.48  ------ Parsing...
% 6.71/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.71/1.48  
% 6.71/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.71/1.48  
% 6.71/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.71/1.48  
% 6.71/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.71/1.48  ------ Proving...
% 6.71/1.48  ------ Problem Properties 
% 6.71/1.48  
% 6.71/1.48  
% 6.71/1.48  clauses                                 43
% 6.71/1.48  conjectures                             20
% 6.71/1.48  EPR                                     16
% 6.71/1.48  Horn                                    24
% 6.71/1.48  unary                                   19
% 6.71/1.48  binary                                  1
% 6.71/1.48  lits                                    269
% 6.71/1.48  lits eq                                 1
% 6.71/1.48  fd_pure                                 0
% 6.71/1.48  fd_pseudo                               0
% 6.71/1.48  fd_cond                                 0
% 6.71/1.48  fd_pseudo_cond                          1
% 6.71/1.48  AC symbols                              0
% 6.71/1.48  
% 6.71/1.48  ------ Schedule dynamic 5 is on 
% 6.71/1.48  
% 6.71/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.71/1.48  
% 6.71/1.48  
% 6.71/1.48  ------ 
% 6.71/1.48  Current options:
% 6.71/1.48  ------ 
% 6.71/1.48  
% 6.71/1.48  ------ Input Options
% 6.71/1.48  
% 6.71/1.48  --out_options                           all
% 6.71/1.48  --tptp_safe_out                         true
% 6.71/1.48  --problem_path                          ""
% 6.71/1.48  --include_path                          ""
% 6.71/1.48  --clausifier                            res/vclausify_rel
% 6.71/1.48  --clausifier_options                    --mode clausify
% 6.71/1.48  --stdin                                 false
% 6.71/1.48  --stats_out                             all
% 6.71/1.48  
% 6.71/1.48  ------ General Options
% 6.71/1.48  
% 6.71/1.48  --fof                                   false
% 6.71/1.48  --time_out_real                         305.
% 6.71/1.48  --time_out_virtual                      -1.
% 6.71/1.48  --symbol_type_check                     false
% 6.71/1.48  --clausify_out                          false
% 6.71/1.48  --sig_cnt_out                           false
% 6.71/1.48  --trig_cnt_out                          false
% 6.71/1.48  --trig_cnt_out_tolerance                1.
% 6.71/1.48  --trig_cnt_out_sk_spl                   false
% 6.71/1.48  --abstr_cl_out                          false
% 6.71/1.48  
% 6.71/1.48  ------ Global Options
% 6.71/1.48  
% 6.71/1.48  --schedule                              default
% 6.71/1.48  --add_important_lit                     false
% 6.71/1.48  --prop_solver_per_cl                    1000
% 6.71/1.48  --min_unsat_core                        false
% 6.71/1.48  --soft_assumptions                      false
% 6.71/1.48  --soft_lemma_size                       3
% 6.71/1.48  --prop_impl_unit_size                   0
% 6.71/1.48  --prop_impl_unit                        []
% 6.71/1.48  --share_sel_clauses                     true
% 6.71/1.48  --reset_solvers                         false
% 6.71/1.48  --bc_imp_inh                            [conj_cone]
% 6.71/1.48  --conj_cone_tolerance                   3.
% 6.71/1.48  --extra_neg_conj                        none
% 6.71/1.48  --large_theory_mode                     true
% 6.71/1.48  --prolific_symb_bound                   200
% 6.71/1.48  --lt_threshold                          2000
% 6.71/1.48  --clause_weak_htbl                      true
% 6.71/1.48  --gc_record_bc_elim                     false
% 6.71/1.48  
% 6.71/1.48  ------ Preprocessing Options
% 6.71/1.48  
% 6.71/1.48  --preprocessing_flag                    true
% 6.71/1.48  --time_out_prep_mult                    0.1
% 6.71/1.48  --splitting_mode                        input
% 6.71/1.48  --splitting_grd                         true
% 6.71/1.48  --splitting_cvd                         false
% 6.71/1.48  --splitting_cvd_svl                     false
% 6.71/1.48  --splitting_nvd                         32
% 6.71/1.48  --sub_typing                            true
% 6.71/1.48  --prep_gs_sim                           true
% 6.71/1.48  --prep_unflatten                        true
% 6.71/1.48  --prep_res_sim                          true
% 6.71/1.48  --prep_upred                            true
% 6.71/1.48  --prep_sem_filter                       exhaustive
% 6.71/1.48  --prep_sem_filter_out                   false
% 6.71/1.48  --pred_elim                             true
% 6.71/1.48  --res_sim_input                         true
% 6.71/1.48  --eq_ax_congr_red                       true
% 6.71/1.48  --pure_diseq_elim                       true
% 6.71/1.48  --brand_transform                       false
% 6.71/1.48  --non_eq_to_eq                          false
% 6.71/1.48  --prep_def_merge                        true
% 6.71/1.48  --prep_def_merge_prop_impl              false
% 6.71/1.48  --prep_def_merge_mbd                    true
% 6.71/1.48  --prep_def_merge_tr_red                 false
% 6.71/1.48  --prep_def_merge_tr_cl                  false
% 6.71/1.48  --smt_preprocessing                     true
% 6.71/1.48  --smt_ac_axioms                         fast
% 6.71/1.48  --preprocessed_out                      false
% 6.71/1.48  --preprocessed_stats                    false
% 6.71/1.48  
% 6.71/1.48  ------ Abstraction refinement Options
% 6.71/1.48  
% 6.71/1.48  --abstr_ref                             []
% 6.71/1.48  --abstr_ref_prep                        false
% 6.71/1.48  --abstr_ref_until_sat                   false
% 6.71/1.48  --abstr_ref_sig_restrict                funpre
% 6.71/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.71/1.48  --abstr_ref_under                       []
% 6.71/1.48  
% 6.71/1.48  ------ SAT Options
% 6.71/1.48  
% 6.71/1.48  --sat_mode                              false
% 6.71/1.48  --sat_fm_restart_options                ""
% 6.71/1.48  --sat_gr_def                            false
% 6.71/1.48  --sat_epr_types                         true
% 6.71/1.48  --sat_non_cyclic_types                  false
% 6.71/1.48  --sat_finite_models                     false
% 6.71/1.48  --sat_fm_lemmas                         false
% 6.71/1.48  --sat_fm_prep                           false
% 6.71/1.48  --sat_fm_uc_incr                        true
% 6.71/1.48  --sat_out_model                         small
% 6.71/1.48  --sat_out_clauses                       false
% 6.71/1.48  
% 6.71/1.48  ------ QBF Options
% 6.71/1.48  
% 6.71/1.48  --qbf_mode                              false
% 6.71/1.48  --qbf_elim_univ                         false
% 6.71/1.48  --qbf_dom_inst                          none
% 6.71/1.48  --qbf_dom_pre_inst                      false
% 6.71/1.48  --qbf_sk_in                             false
% 6.71/1.48  --qbf_pred_elim                         true
% 6.71/1.48  --qbf_split                             512
% 6.71/1.48  
% 6.71/1.48  ------ BMC1 Options
% 6.71/1.48  
% 6.71/1.48  --bmc1_incremental                      false
% 6.71/1.48  --bmc1_axioms                           reachable_all
% 6.71/1.48  --bmc1_min_bound                        0
% 6.71/1.48  --bmc1_max_bound                        -1
% 6.71/1.48  --bmc1_max_bound_default                -1
% 6.71/1.48  --bmc1_symbol_reachability              true
% 6.71/1.48  --bmc1_property_lemmas                  false
% 6.71/1.48  --bmc1_k_induction                      false
% 6.71/1.48  --bmc1_non_equiv_states                 false
% 6.71/1.48  --bmc1_deadlock                         false
% 6.71/1.48  --bmc1_ucm                              false
% 6.71/1.48  --bmc1_add_unsat_core                   none
% 6.71/1.48  --bmc1_unsat_core_children              false
% 6.71/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.71/1.48  --bmc1_out_stat                         full
% 6.71/1.48  --bmc1_ground_init                      false
% 6.71/1.48  --bmc1_pre_inst_next_state              false
% 6.71/1.48  --bmc1_pre_inst_state                   false
% 6.71/1.48  --bmc1_pre_inst_reach_state             false
% 6.71/1.48  --bmc1_out_unsat_core                   false
% 6.71/1.48  --bmc1_aig_witness_out                  false
% 6.71/1.48  --bmc1_verbose                          false
% 6.71/1.48  --bmc1_dump_clauses_tptp                false
% 6.71/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.71/1.48  --bmc1_dump_file                        -
% 6.71/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.71/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.71/1.48  --bmc1_ucm_extend_mode                  1
% 6.71/1.48  --bmc1_ucm_init_mode                    2
% 6.71/1.48  --bmc1_ucm_cone_mode                    none
% 6.71/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.71/1.48  --bmc1_ucm_relax_model                  4
% 6.71/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.71/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.71/1.48  --bmc1_ucm_layered_model                none
% 6.71/1.48  --bmc1_ucm_max_lemma_size               10
% 6.71/1.48  
% 6.71/1.48  ------ AIG Options
% 6.71/1.48  
% 6.71/1.48  --aig_mode                              false
% 6.71/1.48  
% 6.71/1.48  ------ Instantiation Options
% 6.71/1.48  
% 6.71/1.48  --instantiation_flag                    true
% 6.71/1.48  --inst_sos_flag                         false
% 6.71/1.48  --inst_sos_phase                        true
% 6.71/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.71/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.71/1.48  --inst_lit_sel_side                     none
% 6.71/1.48  --inst_solver_per_active                1400
% 6.71/1.48  --inst_solver_calls_frac                1.
% 6.71/1.48  --inst_passive_queue_type               priority_queues
% 6.71/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.71/1.48  --inst_passive_queues_freq              [25;2]
% 6.71/1.48  --inst_dismatching                      true
% 6.71/1.48  --inst_eager_unprocessed_to_passive     true
% 6.71/1.48  --inst_prop_sim_given                   true
% 6.71/1.48  --inst_prop_sim_new                     false
% 6.71/1.48  --inst_subs_new                         false
% 6.71/1.48  --inst_eq_res_simp                      false
% 6.71/1.48  --inst_subs_given                       false
% 6.71/1.48  --inst_orphan_elimination               true
% 6.71/1.48  --inst_learning_loop_flag               true
% 6.71/1.48  --inst_learning_start                   3000
% 6.71/1.48  --inst_learning_factor                  2
% 6.71/1.48  --inst_start_prop_sim_after_learn       3
% 6.71/1.48  --inst_sel_renew                        solver
% 6.71/1.48  --inst_lit_activity_flag                true
% 6.71/1.48  --inst_restr_to_given                   false
% 6.71/1.48  --inst_activity_threshold               500
% 6.71/1.48  --inst_out_proof                        true
% 6.71/1.48  
% 6.71/1.48  ------ Resolution Options
% 6.71/1.48  
% 6.71/1.48  --resolution_flag                       false
% 6.71/1.48  --res_lit_sel                           adaptive
% 6.71/1.48  --res_lit_sel_side                      none
% 6.71/1.48  --res_ordering                          kbo
% 6.71/1.48  --res_to_prop_solver                    active
% 6.71/1.48  --res_prop_simpl_new                    false
% 6.71/1.48  --res_prop_simpl_given                  true
% 6.71/1.48  --res_passive_queue_type                priority_queues
% 6.71/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.71/1.48  --res_passive_queues_freq               [15;5]
% 6.71/1.48  --res_forward_subs                      full
% 6.71/1.48  --res_backward_subs                     full
% 6.71/1.48  --res_forward_subs_resolution           true
% 6.71/1.48  --res_backward_subs_resolution          true
% 6.71/1.48  --res_orphan_elimination                true
% 6.71/1.48  --res_time_limit                        2.
% 6.71/1.48  --res_out_proof                         true
% 6.71/1.48  
% 6.71/1.48  ------ Superposition Options
% 6.71/1.48  
% 6.71/1.48  --superposition_flag                    true
% 6.71/1.48  --sup_passive_queue_type                priority_queues
% 6.71/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.71/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.71/1.48  --demod_completeness_check              fast
% 6.71/1.48  --demod_use_ground                      true
% 6.71/1.48  --sup_to_prop_solver                    passive
% 6.71/1.48  --sup_prop_simpl_new                    true
% 6.71/1.48  --sup_prop_simpl_given                  true
% 6.71/1.48  --sup_fun_splitting                     false
% 6.71/1.48  --sup_smt_interval                      50000
% 6.71/1.48  
% 6.71/1.48  ------ Superposition Simplification Setup
% 6.71/1.48  
% 6.71/1.48  --sup_indices_passive                   []
% 6.71/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.71/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.71/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.71/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.71/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.71/1.48  --sup_full_bw                           [BwDemod]
% 6.71/1.48  --sup_immed_triv                        [TrivRules]
% 6.71/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.71/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.71/1.48  --sup_immed_bw_main                     []
% 6.71/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.71/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.71/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.71/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.71/1.48  
% 6.71/1.48  ------ Combination Options
% 6.71/1.48  
% 6.71/1.48  --comb_res_mult                         3
% 6.71/1.48  --comb_sup_mult                         2
% 6.71/1.48  --comb_inst_mult                        10
% 6.71/1.48  
% 6.71/1.48  ------ Debug Options
% 6.71/1.48  
% 6.71/1.48  --dbg_backtrace                         false
% 6.71/1.48  --dbg_dump_prop_clauses                 false
% 6.71/1.48  --dbg_dump_prop_clauses_file            -
% 6.71/1.48  --dbg_out_stat                          false
% 6.71/1.48  
% 6.71/1.48  
% 6.71/1.48  
% 6.71/1.48  
% 6.71/1.48  ------ Proving...
% 6.71/1.48  
% 6.71/1.48  
% 6.71/1.48  % SZS status Theorem for theBenchmark.p
% 6.71/1.48  
% 6.71/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.71/1.48  
% 6.71/1.48  fof(f9,conjecture,(
% 6.71/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 6.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.71/1.48  
% 6.71/1.48  fof(f10,negated_conjecture,(
% 6.71/1.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)))))))))))),
% 6.71/1.48    inference(negated_conjecture,[],[f9])).
% 6.71/1.48  
% 6.71/1.48  fof(f26,plain,(
% 6.71/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : (((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & (r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4))) & ~r1_tsep_1(X2,X3)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 6.71/1.48    inference(ennf_transformation,[],[f10])).
% 6.71/1.48  
% 6.71/1.48  fof(f27,plain,(
% 6.71/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.71/1.48    inference(flattening,[],[f26])).
% 6.71/1.48  
% 6.71/1.48  fof(f45,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,sK7),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,sK7),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,sK7))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(sK7,X3,X1) & v1_funct_2(sK7,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(sK7))) )),
% 6.71/1.48    introduced(choice_axiom,[])).
% 6.71/1.48  
% 6.71/1.48  fof(f44,plain,(
% 6.71/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,sK6,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,sK6,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,sK6,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),sK6),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(sK6,X2,X1) & v1_funct_2(sK6,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(sK6))) )),
% 6.71/1.48    introduced(choice_axiom,[])).
% 6.71/1.48  
% 6.71/1.48  fof(f43,plain,(
% 6.71/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,sK5,X4,X5),k1_tsep_1(X0,X2,sK5),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,sK5,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,sK5)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,sK5,X4,X5))) & r4_tsep_1(X0,X2,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,sK5),X4),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,X2,sK5),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1)))) & v5_pre_topc(X5,sK5,X1) & v1_funct_2(X5,u1_struct_0(sK5),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,sK5) & m1_pre_topc(sK5,X0) & ~v2_struct_0(sK5))) )),
% 6.71/1.48    introduced(choice_axiom,[])).
% 6.71/1.48  
% 6.71/1.48  fof(f42,plain,(
% 6.71/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,sK4,X3,X4,X5),k1_tsep_1(X0,sK4,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,sK4,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,sK4,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,sK4,X3,X4,X5))) & r4_tsep_1(X0,sK4,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,sK4,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1)))) & v5_pre_topc(X4,sK4,X1) & v1_funct_2(X4,u1_struct_0(sK4),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(sK4,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 6.71/1.48    introduced(choice_axiom,[])).
% 6.71/1.48  
% 6.71/1.48  fof(f41,plain,(
% 6.71/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(X0,sK3,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),sK3) | ~v1_funct_2(k10_tmap_1(X0,sK3,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(X0,sK3,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(sK3),k3_tmap_1(X0,sK3,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,sK3,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(X5,X3,sK3) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(X4,X2,sK3) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))) )),
% 6.71/1.48    introduced(choice_axiom,[])).
% 6.71/1.48  
% 6.71/1.48  fof(f40,plain,(
% 6.71/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) & r4_tsep_1(X0,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((~m1_subset_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k10_tmap_1(sK2,X1,X2,X3,X4,X5),k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(k10_tmap_1(sK2,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k10_tmap_1(sK2,X1,X2,X3,X4,X5))) & r4_tsep_1(sK2,X2,X3) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK2,X1,X2,k2_tsep_1(sK2,X2,X3),X4),k3_tmap_1(sK2,X1,X3,k2_tsep_1(sK2,X2,X3),X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(X5,X3,X1) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(X4,X2,X1) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) & ~r1_tsep_1(X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 6.71/1.48    introduced(choice_axiom,[])).
% 6.71/1.48  
% 6.71/1.48  fof(f46,plain,(
% 6.71/1.48    ((((((~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) & r4_tsep_1(sK2,sK4,sK5) & r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(sK7,sK5,sK3) & v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(sK6,sK4,sK3) & v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(sK6)) & ~r1_tsep_1(sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 6.71/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f27,f45,f44,f43,f42,f41,f40])).
% 6.71/1.48  
% 6.71/1.48  fof(f95,plain,(
% 6.71/1.48    r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f5,axiom,(
% 6.71/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5)) => ((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))))))))))),
% 6.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.71/1.48  
% 6.71/1.48  fof(f19,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | r1_tsep_1(X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.71/1.48    inference(ennf_transformation,[],[f5])).
% 6.71/1.48  
% 6.71/1.48  fof(f20,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.71/1.48    inference(flattening,[],[f19])).
% 6.71/1.48  
% 6.71/1.48  fof(f38,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) & (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | (~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.71/1.48    inference(nnf_transformation,[],[f20])).
% 6.71/1.48  
% 6.71/1.48  fof(f39,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((((r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) & r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4)) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))) & (r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.71/1.48    inference(flattening,[],[f38])).
% 6.71/1.48  
% 6.71/1.48  fof(f72,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X5) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f39])).
% 6.71/1.48  
% 6.71/1.48  fof(f86,plain,(
% 6.71/1.48    ~r1_tsep_1(sK4,sK5)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f82,plain,(
% 6.71/1.48    ~v2_struct_0(sK4)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f84,plain,(
% 6.71/1.48    ~v2_struct_0(sK5)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f76,plain,(
% 6.71/1.48    ~v2_struct_0(sK2)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f77,plain,(
% 6.71/1.48    v2_pre_topc(sK2)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f78,plain,(
% 6.71/1.48    l1_pre_topc(sK2)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f79,plain,(
% 6.71/1.48    ~v2_struct_0(sK3)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f80,plain,(
% 6.71/1.48    v2_pre_topc(sK3)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f81,plain,(
% 6.71/1.48    l1_pre_topc(sK3)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f83,plain,(
% 6.71/1.48    m1_pre_topc(sK4,sK2)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f85,plain,(
% 6.71/1.48    m1_pre_topc(sK5,sK2)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f87,plain,(
% 6.71/1.48    v1_funct_1(sK6)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f88,plain,(
% 6.71/1.48    v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3))),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f90,plain,(
% 6.71/1.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f91,plain,(
% 6.71/1.48    v1_funct_1(sK7)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f92,plain,(
% 6.71/1.48    v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f94,plain,(
% 6.71/1.48    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f3,axiom,(
% 6.71/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 6.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.71/1.48  
% 6.71/1.48  fof(f15,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.71/1.48    inference(ennf_transformation,[],[f3])).
% 6.71/1.48  
% 6.71/1.48  fof(f16,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.71/1.48    inference(flattening,[],[f15])).
% 6.71/1.48  
% 6.71/1.48  fof(f54,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f16])).
% 6.71/1.48  
% 6.71/1.48  fof(f1,axiom,(
% 6.71/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 6.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.71/1.48  
% 6.71/1.48  fof(f11,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.71/1.48    inference(ennf_transformation,[],[f1])).
% 6.71/1.48  
% 6.71/1.48  fof(f12,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.71/1.48    inference(flattening,[],[f11])).
% 6.71/1.48  
% 6.71/1.48  fof(f31,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.71/1.48    inference(nnf_transformation,[],[f12])).
% 6.71/1.48  
% 6.71/1.48  fof(f47,plain,(
% 6.71/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f31])).
% 6.71/1.48  
% 6.71/1.48  fof(f52,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f16])).
% 6.71/1.48  
% 6.71/1.48  fof(f53,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f16])).
% 6.71/1.48  
% 6.71/1.48  fof(f7,axiom,(
% 6.71/1.48    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 6.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.71/1.48  
% 6.71/1.48  fof(f23,plain,(
% 6.71/1.48    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 6.71/1.48    inference(ennf_transformation,[],[f7])).
% 6.71/1.48  
% 6.71/1.48  fof(f74,plain,(
% 6.71/1.48    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f23])).
% 6.71/1.48  
% 6.71/1.48  fof(f2,axiom,(
% 6.71/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 6.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.71/1.48  
% 6.71/1.48  fof(f13,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.71/1.48    inference(ennf_transformation,[],[f2])).
% 6.71/1.48  
% 6.71/1.48  fof(f14,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.71/1.48    inference(flattening,[],[f13])).
% 6.71/1.48  
% 6.71/1.48  fof(f49,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f14])).
% 6.71/1.48  
% 6.71/1.48  fof(f50,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f14])).
% 6.71/1.48  
% 6.71/1.48  fof(f51,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f14])).
% 6.71/1.48  
% 6.71/1.48  fof(f6,axiom,(
% 6.71/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 6.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.71/1.48  
% 6.71/1.48  fof(f21,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | (~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.71/1.48    inference(ennf_transformation,[],[f6])).
% 6.71/1.48  
% 6.71/1.48  fof(f22,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.71/1.48    inference(flattening,[],[f21])).
% 6.71/1.48  
% 6.71/1.48  fof(f73,plain,(
% 6.71/1.48    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f22])).
% 6.71/1.48  
% 6.71/1.48  fof(f28,plain,(
% 6.71/1.48    ! [X1,X3,X4,X2,X0] : (sP0(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 6.71/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.71/1.48  
% 6.71/1.48  fof(f35,plain,(
% 6.71/1.48    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 6.71/1.48    inference(nnf_transformation,[],[f28])).
% 6.71/1.48  
% 6.71/1.48  fof(f36,plain,(
% 6.71/1.48    ! [X1,X3,X4,X2,X0] : ((sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP0(X1,X3,X4,X2,X0)))),
% 6.71/1.48    inference(flattening,[],[f35])).
% 6.71/1.48  
% 6.71/1.48  fof(f37,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP0(X0,X1,X2,X3,X4)))),
% 6.71/1.48    inference(rectify,[],[f36])).
% 6.71/1.48  
% 6.71/1.48  fof(f68,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X3,X1] : (sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 6.71/1.48    inference(cnf_transformation,[],[f37])).
% 6.71/1.48  
% 6.71/1.48  fof(f29,plain,(
% 6.71/1.48    ! [X0,X2,X4,X3,X1] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> sP0(X1,X3,X4,X2,X0)) | ~sP1(X0,X2,X4,X3,X1))),
% 6.71/1.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.71/1.48  
% 6.71/1.48  fof(f32,plain,(
% 6.71/1.48    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)))) | ~sP1(X0,X2,X4,X3,X1))),
% 6.71/1.48    inference(nnf_transformation,[],[f29])).
% 6.71/1.48  
% 6.71/1.48  fof(f33,plain,(
% 6.71/1.48    ! [X0,X2,X4,X3,X1] : ((((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X4,X2,X0)) & (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~sP1(X0,X2,X4,X3,X1))),
% 6.71/1.48    inference(flattening,[],[f32])).
% 6.71/1.48  
% 6.71/1.48  fof(f34,plain,(
% 6.71/1.48    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) & v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) & v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) & v1_funct_1(X2)) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4)) | ~v1_funct_1(X2))) | ~sP1(X0,X1,X2,X3,X4))),
% 6.71/1.48    inference(rectify,[],[f33])).
% 6.71/1.48  
% 6.71/1.48  fof(f58,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) | ~sP0(X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f34])).
% 6.71/1.48  
% 6.71/1.48  fof(f4,axiom,(
% 6.71/1.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 6.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.71/1.48  
% 6.71/1.48  fof(f17,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.71/1.48    inference(ennf_transformation,[],[f4])).
% 6.71/1.48  
% 6.71/1.48  fof(f18,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.71/1.48    inference(flattening,[],[f17])).
% 6.71/1.48  
% 6.71/1.48  fof(f30,plain,(
% 6.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.71/1.48    inference(definition_folding,[],[f18,f29,f28])).
% 6.71/1.48  
% 6.71/1.48  fof(f69,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X2,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f30])).
% 6.71/1.48  
% 6.71/1.48  fof(f96,plain,(
% 6.71/1.48    r4_tsep_1(sK2,sK4,sK5)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f71,plain,(
% 6.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,k10_tmap_1(X0,X1,X2,X3,X4,X5)),X4) | ~r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.71/1.48    inference(cnf_transformation,[],[f39])).
% 6.71/1.48  
% 6.71/1.48  fof(f97,plain,(
% 6.71/1.48    ~m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f93,plain,(
% 6.71/1.48    v5_pre_topc(sK7,sK5,sK3)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  fof(f89,plain,(
% 6.71/1.48    v5_pre_topc(sK6,sK4,sK3)),
% 6.71/1.48    inference(cnf_transformation,[],[f46])).
% 6.71/1.48  
% 6.71/1.48  cnf(c_31,negated_conjecture,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
% 6.71/1.48      inference(cnf_transformation,[],[f95]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1527,negated_conjecture,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_31]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2278,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_1527]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_23,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
% 6.71/1.48      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
% 6.71/1.48      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 6.71/1.48      | r1_tsep_1(X3,X0)
% 6.71/1.48      | ~ m1_pre_topc(X0,X2)
% 6.71/1.48      | ~ m1_pre_topc(X3,X2)
% 6.71/1.48      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X3)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | ~ v1_funct_1(X5)
% 6.71/1.48      | ~ v1_funct_1(X4) ),
% 6.71/1.48      inference(cnf_transformation,[],[f72]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_40,negated_conjecture,
% 6.71/1.48      ( ~ r1_tsep_1(sK4,sK5) ),
% 6.71/1.48      inference(cnf_transformation,[],[f86]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_723,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X3,X0),X0,k10_tmap_1(X2,X1,X3,X0,X4,X5)),X5)
% 6.71/1.48      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X3,X0)),u1_struct_0(X1),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X3,X0),X4),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X3,X0),X5))
% 6.71/1.48      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X5,u1_struct_0(X0),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(X0,X2)
% 6.71/1.48      | ~ m1_pre_topc(X3,X2)
% 6.71/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X3)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | ~ v1_funct_1(X5)
% 6.71/1.48      | ~ v1_funct_1(X4)
% 6.71/1.48      | sK5 != X0
% 6.71/1.48      | sK4 != X3 ),
% 6.71/1.48      inference(resolution_lifted,[status(thm)],[c_23,c_40]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_724,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0)
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK4)
% 6.71/1.48      | ~ v1_funct_1(X3)
% 6.71/1.48      | ~ v1_funct_1(X2) ),
% 6.71/1.48      inference(unflattening,[status(thm)],[c_723]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_44,negated_conjecture,
% 6.71/1.48      ( ~ v2_struct_0(sK4) ),
% 6.71/1.48      inference(cnf_transformation,[],[f82]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_42,negated_conjecture,
% 6.71/1.48      ( ~ v2_struct_0(sK5) ),
% 6.71/1.48      inference(cnf_transformation,[],[f84]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_728,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0)
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | ~ v1_funct_1(X3)
% 6.71/1.48      | ~ v1_funct_1(X2) ),
% 6.71/1.48      inference(global_propositional_subsumption,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_724,c_44,c_42]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_729,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK5,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X3)
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0)
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | ~ v1_funct_1(X2)
% 6.71/1.48      | ~ v1_funct_1(X3) ),
% 6.71/1.48      inference(renaming,[status(thm)],[c_728]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1507,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,sK4,k2_tsep_1(X0_55,sK4,sK5),X0_54),k3_tmap_1(X0_55,X1_55,sK5,k2_tsep_1(X0_55,sK4,sK5),X1_54))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54)),X1_54)
% 6.71/1.48      | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55))
% 6.71/1.48      | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55))
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0_55)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0_55)
% 6.71/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X0_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X0_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(X1_54) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_729]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2298,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,sK4,k2_tsep_1(X0_55,sK4,sK5),X0_54),k3_tmap_1(X0_55,X1_55,sK5,k2_tsep_1(X0_55,sK4,sK5),X1_54)) != iProver_top
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK5,k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54)),X1_54) = iProver_top
% 6.71/1.48      | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,X0_55) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,X0_55) != iProver_top
% 6.71/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | v2_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | v2_struct_0(X1_55) = iProver_top
% 6.71/1.48      | v2_struct_0(X0_55) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(X1_54) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_1507]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_6503,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(superposition,[status(thm)],[c_2278,c_2298]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_50,negated_conjecture,
% 6.71/1.48      ( ~ v2_struct_0(sK2) ),
% 6.71/1.48      inference(cnf_transformation,[],[f76]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_51,plain,
% 6.71/1.48      ( v2_struct_0(sK2) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_49,negated_conjecture,
% 6.71/1.48      ( v2_pre_topc(sK2) ),
% 6.71/1.48      inference(cnf_transformation,[],[f77]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_52,plain,
% 6.71/1.48      ( v2_pre_topc(sK2) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_48,negated_conjecture,
% 6.71/1.48      ( l1_pre_topc(sK2) ),
% 6.71/1.48      inference(cnf_transformation,[],[f78]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_53,plain,
% 6.71/1.48      ( l1_pre_topc(sK2) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_47,negated_conjecture,
% 6.71/1.48      ( ~ v2_struct_0(sK3) ),
% 6.71/1.48      inference(cnf_transformation,[],[f79]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_54,plain,
% 6.71/1.48      ( v2_struct_0(sK3) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_46,negated_conjecture,
% 6.71/1.48      ( v2_pre_topc(sK3) ),
% 6.71/1.48      inference(cnf_transformation,[],[f80]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_55,plain,
% 6.71/1.48      ( v2_pre_topc(sK3) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_45,negated_conjecture,
% 6.71/1.48      ( l1_pre_topc(sK3) ),
% 6.71/1.48      inference(cnf_transformation,[],[f81]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_56,plain,
% 6.71/1.48      ( l1_pre_topc(sK3) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_43,negated_conjecture,
% 6.71/1.48      ( m1_pre_topc(sK4,sK2) ),
% 6.71/1.48      inference(cnf_transformation,[],[f83]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_58,plain,
% 6.71/1.48      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_41,negated_conjecture,
% 6.71/1.48      ( m1_pre_topc(sK5,sK2) ),
% 6.71/1.48      inference(cnf_transformation,[],[f85]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_60,plain,
% 6.71/1.48      ( m1_pre_topc(sK5,sK2) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_39,negated_conjecture,
% 6.71/1.48      ( v1_funct_1(sK6) ),
% 6.71/1.48      inference(cnf_transformation,[],[f87]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_62,plain,
% 6.71/1.48      ( v1_funct_1(sK6) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_38,negated_conjecture,
% 6.71/1.48      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) ),
% 6.71/1.48      inference(cnf_transformation,[],[f88]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_63,plain,
% 6.71/1.48      ( v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_36,negated_conjecture,
% 6.71/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
% 6.71/1.48      inference(cnf_transformation,[],[f90]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_65,plain,
% 6.71/1.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_35,negated_conjecture,
% 6.71/1.48      ( v1_funct_1(sK7) ),
% 6.71/1.48      inference(cnf_transformation,[],[f91]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_66,plain,
% 6.71/1.48      ( v1_funct_1(sK7) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_34,negated_conjecture,
% 6.71/1.48      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) ),
% 6.71/1.48      inference(cnf_transformation,[],[f92]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_67,plain,
% 6.71/1.48      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_32,negated_conjecture,
% 6.71/1.48      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
% 6.71/1.48      inference(cnf_transformation,[],[f94]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_69,plain,
% 6.71/1.48      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_70,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2950,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,X0_55,sK5,k2_tsep_1(sK2,sK4,sK5),X1_54))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,X0_55,sK4,sK5,X0_54,X1_54)),X1_54)
% 6.71/1.48      | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55))
% 6.71/1.48      | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X0_55))
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
% 6.71/1.48      | ~ v2_pre_topc(X0_55)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(X0_55)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(X1_54) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_1507]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3318,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),sK7)
% 6.71/1.48      | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_2950]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3319,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),sK7) = iProver_top
% 6.71/1.48      | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_3318]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3321,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3319]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_6506,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(sK5),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK7) = iProver_top ),
% 6.71/1.48      inference(global_propositional_subsumption,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_6503,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_60,c_62,
% 6.71/1.48                 c_63,c_65,c_66,c_67,c_69,c_70,c_3321]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_5,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.71/1.48      | ~ m1_pre_topc(X3,X4)
% 6.71/1.48      | ~ m1_pre_topc(X1,X4)
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.71/1.48      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ v2_pre_topc(X4)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X4)
% 6.71/1.48      | v2_struct_0(X4)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | ~ v1_funct_1(X0) ),
% 6.71/1.48      inference(cnf_transformation,[],[f54]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1534,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 6.71/1.48      | ~ m1_pre_topc(X2_55,X3_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X3_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 6.71/1.48      | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X3_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X3_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X3_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2271,plain,
% 6.71/1.48      ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 6.71/1.48      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | m1_subset_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) = iProver_top
% 6.71/1.48      | v2_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | v2_pre_topc(X3_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X3_55) != iProver_top
% 6.71/1.48      | v2_struct_0(X1_55) = iProver_top
% 6.71/1.48      | v2_struct_0(X3_55) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_1534]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1,plain,
% 6.71/1.48      ( ~ r2_funct_2(X0,X1,X2,X3)
% 6.71/1.48      | ~ v1_funct_2(X3,X0,X1)
% 6.71/1.48      | ~ v1_funct_2(X2,X0,X1)
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.71/1.48      | ~ v1_funct_1(X3)
% 6.71/1.48      | ~ v1_funct_1(X2)
% 6.71/1.48      | X2 = X3 ),
% 6.71/1.48      inference(cnf_transformation,[],[f47]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1538,plain,
% 6.71/1.48      ( ~ r2_funct_2(X0_56,X1_56,X0_54,X1_54)
% 6.71/1.48      | ~ v1_funct_2(X1_54,X0_56,X1_56)
% 6.71/1.48      | ~ v1_funct_2(X0_54,X0_56,X1_56)
% 6.71/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(X1_54)
% 6.71/1.48      | X0_54 = X1_54 ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2267,plain,
% 6.71/1.48      ( X0_54 = X1_54
% 6.71/1.48      | r2_funct_2(X0_56,X1_56,X0_54,X1_54) != iProver_top
% 6.71/1.48      | v1_funct_2(X0_54,X0_56,X1_56) != iProver_top
% 6.71/1.48      | v1_funct_2(X1_54,X0_56,X1_56) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 6.71/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(X1_54) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_1538]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_4669,plain,
% 6.71/1.48      ( k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54) = X1_54
% 6.71/1.48      | r2_funct_2(u1_struct_0(X3_55),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54),X1_54) != iProver_top
% 6.71/1.48      | v1_funct_2(X0_54,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | v1_funct_2(X1_54,u1_struct_0(X3_55),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | v1_funct_2(k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54),u1_struct_0(X3_55),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | m1_pre_topc(X3_55,X0_55) != iProver_top
% 6.71/1.48      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | v2_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | v2_struct_0(X1_55) = iProver_top
% 6.71/1.48      | v2_struct_0(X0_55) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(X1_54) != iProver_top
% 6.71/1.48      | v1_funct_1(k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54)) != iProver_top ),
% 6.71/1.48      inference(superposition,[status(thm)],[c_2271,c_2267]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_7,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.71/1.48      | ~ m1_pre_topc(X3,X4)
% 6.71/1.48      | ~ m1_pre_topc(X1,X4)
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ v2_pre_topc(X4)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X4)
% 6.71/1.48      | v2_struct_0(X4)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | ~ v1_funct_1(X0)
% 6.71/1.48      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 6.71/1.48      inference(cnf_transformation,[],[f52]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1532,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 6.71/1.48      | ~ m1_pre_topc(X2_55,X3_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X3_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X3_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X3_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X3_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54)) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2273,plain,
% 6.71/1.48      ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | m1_pre_topc(X2_55,X3_55) != iProver_top
% 6.71/1.48      | m1_pre_topc(X0_55,X3_55) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | v2_pre_topc(X3_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X3_55) != iProver_top
% 6.71/1.48      | v2_struct_0(X1_55) = iProver_top
% 6.71/1.48      | v2_struct_0(X3_55) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(k3_tmap_1(X3_55,X1_55,X0_55,X2_55,X0_54)) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_1532]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_6,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.71/1.48      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 6.71/1.48      | ~ m1_pre_topc(X4,X3)
% 6.71/1.48      | ~ m1_pre_topc(X1,X3)
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ v2_pre_topc(X3)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X3)
% 6.71/1.48      | v2_struct_0(X3)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | ~ v1_funct_1(X0) ),
% 6.71/1.48      inference(cnf_transformation,[],[f53]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1533,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 6.71/1.48      | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_54),u1_struct_0(X3_55),u1_struct_0(X1_55))
% 6.71/1.48      | ~ m1_pre_topc(X3_55,X2_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X2_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X2_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X2_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X2_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2272,plain,
% 6.71/1.48      ( v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | v1_funct_2(k3_tmap_1(X2_55,X1_55,X0_55,X3_55,X0_54),u1_struct_0(X3_55),u1_struct_0(X1_55)) = iProver_top
% 6.71/1.48      | m1_pre_topc(X3_55,X2_55) != iProver_top
% 6.71/1.48      | m1_pre_topc(X0_55,X2_55) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | v2_pre_topc(X2_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X2_55) != iProver_top
% 6.71/1.48      | v2_struct_0(X1_55) = iProver_top
% 6.71/1.48      | v2_struct_0(X2_55) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_1533]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_9465,plain,
% 6.71/1.48      ( k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54) = X1_54
% 6.71/1.48      | r2_funct_2(u1_struct_0(X3_55),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,X2_55,X3_55,X0_54),X1_54) != iProver_top
% 6.71/1.48      | v1_funct_2(X1_54,u1_struct_0(X3_55),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | v1_funct_2(X0_54,u1_struct_0(X2_55),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | m1_pre_topc(X2_55,X0_55) != iProver_top
% 6.71/1.48      | m1_pre_topc(X3_55,X0_55) != iProver_top
% 6.71/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3_55),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | v2_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | v2_struct_0(X1_55) = iProver_top
% 6.71/1.48      | v2_struct_0(X0_55) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(X1_54) != iProver_top ),
% 6.71/1.48      inference(forward_subsumption_resolution,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_4669,c_2273,c_2272]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_9471,plain,
% 6.71/1.48      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7
% 6.71/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top ),
% 6.71/1.48      inference(superposition,[status(thm)],[c_6506,c_9465]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_57,plain,
% 6.71/1.48      ( v2_struct_0(sK4) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_59,plain,
% 6.71/1.48      ( v2_struct_0(sK5) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_27,plain,
% 6.71/1.48      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 6.71/1.48      inference(cnf_transformation,[],[f74]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1530,plain,
% 6.71/1.48      ( m1_pre_topc(X0_55,X0_55) | ~ l1_pre_topc(X0_55) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_27]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3700,plain,
% 6.71/1.48      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_1530]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3703,plain,
% 6.71/1.48      ( m1_pre_topc(sK2,sK2) = iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_3700]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_4,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 6.71/1.48      | ~ m1_pre_topc(X1,X5)
% 6.71/1.48      | ~ m1_pre_topc(X4,X5)
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ v2_pre_topc(X5)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X5)
% 6.71/1.48      | v2_struct_0(X5)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | v2_struct_0(X4)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | ~ v1_funct_1(X0)
% 6.71/1.48      | ~ v1_funct_1(X3)
% 6.71/1.48      | v1_funct_1(k10_tmap_1(X5,X2,X4,X1,X3,X0)) ),
% 6.71/1.48      inference(cnf_transformation,[],[f49]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1535,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 6.71/1.48      | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 6.71/1.48      | ~ m1_pre_topc(X2_55,X3_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X3_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X3_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X3_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(X3_55)
% 6.71/1.48      | v2_struct_0(X2_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(X1_54)
% 6.71/1.48      | v1_funct_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54)) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3059,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(sK5,X1_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | v1_funct_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_54,sK7))
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_1535]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3261,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(X0_55,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,X0_55,sK5,X0_54,sK7))
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3059]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3808,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK4)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7))
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3261]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3809,plain,
% 6.71/1.48      ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK5) = iProver_top
% 6.71/1.48      | v2_struct_0(sK4) = iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)) = iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_3808]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3811,plain,
% 6.71/1.48      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK5) = iProver_top
% 6.71/1.48      | v2_struct_0(sK4) = iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3809]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 6.71/1.48      | v1_funct_2(k10_tmap_1(X5,X2,X4,X1,X3,X0),u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))
% 6.71/1.48      | ~ m1_pre_topc(X1,X5)
% 6.71/1.48      | ~ m1_pre_topc(X4,X5)
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ v2_pre_topc(X5)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X5)
% 6.71/1.48      | v2_struct_0(X5)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | v2_struct_0(X4)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | ~ v1_funct_1(X0)
% 6.71/1.48      | ~ v1_funct_1(X3) ),
% 6.71/1.48      inference(cnf_transformation,[],[f50]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1536,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 6.71/1.48      | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 6.71/1.48      | v1_funct_2(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54),u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))
% 6.71/1.48      | ~ m1_pre_topc(X2_55,X3_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X3_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X3_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X3_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(X3_55)
% 6.71/1.48      | v2_struct_0(X2_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(X1_54) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3069,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
% 6.71/1.48      | v1_funct_2(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(sK5,X1_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_1536]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3281,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
% 6.71/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,X0_55,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,X0_55,sK5)),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(X0_55,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3069]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3838,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
% 6.71/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK4)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3281]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3839,plain,
% 6.71/1.48      ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK5) = iProver_top
% 6.71/1.48      | v2_struct_0(sK4) = iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_3838]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3841,plain,
% 6.71/1.48      ( v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) = iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK5) = iProver_top
% 6.71/1.48      | v2_struct_0(sK4) = iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3839]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 6.71/1.48      | ~ m1_pre_topc(X1,X5)
% 6.71/1.48      | ~ m1_pre_topc(X4,X5)
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 6.71/1.48      | m1_subset_1(k10_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X4,X1)),u1_struct_0(X2))))
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ v2_pre_topc(X5)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X5)
% 6.71/1.48      | v2_struct_0(X5)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | v2_struct_0(X4)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | ~ v1_funct_1(X0)
% 6.71/1.48      | ~ v1_funct_1(X3) ),
% 6.71/1.48      inference(cnf_transformation,[],[f51]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1537,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(X1_55))
% 6.71/1.48      | ~ v1_funct_2(X1_54,u1_struct_0(X2_55),u1_struct_0(X1_55))
% 6.71/1.48      | ~ m1_pre_topc(X2_55,X3_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X3_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_55),u1_struct_0(X1_55))))
% 6.71/1.48      | m1_subset_1(k10_tmap_1(X3_55,X1_55,X2_55,X0_55,X1_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_55,X2_55,X0_55)),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X3_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X3_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(X3_55)
% 6.71/1.48      | v2_struct_0(X2_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(X1_54) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3086,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(sK5,X1_55)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 6.71/1.48      | m1_subset_1(k10_tmap_1(X1_55,sK3,X0_55,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1_55,X0_55,sK5)),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_1537]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3297,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(X0_55),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(X0_55,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_55),u1_struct_0(sK3))))
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,X0_55,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X0_55,sK5)),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3086]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3946,plain,
% 6.71/1.48      ( ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK4)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3297]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3947,plain,
% 6.71/1.48      ( v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK5) = iProver_top
% 6.71/1.48      | v2_struct_0(sK4) = iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_3946]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3949,plain,
% 6.71/1.48      ( v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) = iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK5) = iProver_top
% 6.71/1.48      | v2_struct_0(sK4) = iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3947]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_26,plain,
% 6.71/1.48      ( ~ m1_pre_topc(X0,X1)
% 6.71/1.48      | ~ m1_pre_topc(X2,X1)
% 6.71/1.48      | ~ m1_pre_topc(X3,X2)
% 6.71/1.48      | ~ m1_pre_topc(X3,X1)
% 6.71/1.48      | ~ m1_pre_topc(X0,X2)
% 6.71/1.48      | m1_pre_topc(k1_tsep_1(X1,X3,X0),X2)
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X3)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | v2_struct_0(X0) ),
% 6.71/1.48      inference(cnf_transformation,[],[f73]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1531,plain,
% 6.71/1.48      ( ~ m1_pre_topc(X0_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(X2_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(X3_55,X2_55)
% 6.71/1.48      | ~ m1_pre_topc(X3_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,X2_55)
% 6.71/1.48      | m1_pre_topc(k1_tsep_1(X1_55,X3_55,X0_55),X2_55)
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(X3_55)
% 6.71/1.48      | v2_struct_0(X2_55) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_26]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3706,plain,
% 6.71/1.48      ( ~ m1_pre_topc(X0_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(X2_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,sK2)
% 6.71/1.48      | ~ m1_pre_topc(X2_55,sK2)
% 6.71/1.48      | m1_pre_topc(k1_tsep_1(X1_55,X2_55,X0_55),sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK2,X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(X2_55)
% 6.71/1.48      | v2_struct_0(sK2) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_1531]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_5393,plain,
% 6.71/1.48      ( ~ m1_pre_topc(X0_55,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(X0_55,sK2)
% 6.71/1.48      | m1_pre_topc(k1_tsep_1(X1_55,X0_55,sK5),sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK5,X1_55)
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK2,X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK2) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3706]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_6327,plain,
% 6.71/1.48      ( m1_pre_topc(k1_tsep_1(X0_55,sK4,sK5),sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0_55)
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0_55)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK2,X0_55)
% 6.71/1.48      | ~ v2_pre_topc(X0_55)
% 6.71/1.48      | ~ l1_pre_topc(X0_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK4)
% 6.71/1.48      | v2_struct_0(sK2) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_5393]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_6666,plain,
% 6.71/1.48      ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK2,sK2)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK4)
% 6.71/1.48      | v2_struct_0(sK2) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_6327]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_6667,plain,
% 6.71/1.48      ( m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) = iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK2,sK2) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK5) = iProver_top
% 6.71/1.48      | v2_struct_0(sK4) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_6666]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_10731,plain,
% 6.71/1.48      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK7 ),
% 6.71/1.48      inference(global_propositional_subsumption,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_9471,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,
% 6.71/1.48                 c_60,c_62,c_63,c_65,c_66,c_67,c_69,c_3703,c_3811,c_3841,
% 6.71/1.48                 c_3949,c_6667]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_13,plain,
% 6.71/1.48      ( sP0(X0,X1,X2,X3,X4)
% 6.71/1.48      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0)
% 6.71/1.48      | ~ v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0)
% 6.71/1.48      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0))
% 6.71/1.48      | ~ v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0))
% 6.71/1.48      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
% 6.71/1.48      | ~ m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
% 6.71/1.48      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2))
% 6.71/1.48      | ~ v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) ),
% 6.71/1.48      inference(cnf_transformation,[],[f68]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_9,plain,
% 6.71/1.48      ( ~ sP1(X0,X1,X2,X3,X4)
% 6.71/1.48      | ~ sP0(X4,X3,X2,X1,X0)
% 6.71/1.48      | v5_pre_topc(X2,k1_tsep_1(X0,X1,X3),X4) ),
% 6.71/1.48      inference(cnf_transformation,[],[f58]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_22,plain,
% 6.71/1.48      ( sP1(X0,X1,X2,X3,X4)
% 6.71/1.48      | ~ r4_tsep_1(X0,X1,X3)
% 6.71/1.48      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 6.71/1.48      | ~ m1_pre_topc(X3,X0)
% 6.71/1.48      | ~ m1_pre_topc(X1,X0)
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 6.71/1.48      | ~ v2_pre_topc(X4)
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X4)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(X4)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X3)
% 6.71/1.48      | ~ v1_funct_1(X2) ),
% 6.71/1.48      inference(cnf_transformation,[],[f69]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_30,negated_conjecture,
% 6.71/1.48      ( r4_tsep_1(sK2,sK4,sK5) ),
% 6.71/1.48      inference(cnf_transformation,[],[f96]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_535,plain,
% 6.71/1.48      ( sP1(X0,X1,X2,X3,X4)
% 6.71/1.48      | ~ v1_funct_2(X2,u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))
% 6.71/1.48      | ~ m1_pre_topc(X3,X0)
% 6.71/1.48      | ~ m1_pre_topc(X1,X0)
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X3)),u1_struct_0(X4))))
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ v2_pre_topc(X4)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X4)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X3)
% 6.71/1.48      | v2_struct_0(X4)
% 6.71/1.48      | ~ v1_funct_1(X2)
% 6.71/1.48      | sK5 != X3
% 6.71/1.48      | sK4 != X1
% 6.71/1.48      | sK2 != X0 ),
% 6.71/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_536,plain,
% 6.71/1.48      ( sP1(sK2,sK4,X0,sK5,X1)
% 6.71/1.48      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK4)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0) ),
% 6.71/1.48      inference(unflattening,[status(thm)],[c_535]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_540,plain,
% 6.71/1.48      ( v2_struct_0(X1)
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 6.71/1.48      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 6.71/1.48      | sP1(sK2,sK4,X0,sK5,X1)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ v1_funct_1(X0) ),
% 6.71/1.48      inference(global_propositional_subsumption,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_536,c_50,c_49,c_48,c_44,c_43,c_42,c_41]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_541,plain,
% 6.71/1.48      ( sP1(sK2,sK4,X0,sK5,X1)
% 6.71/1.48      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | ~ v1_funct_1(X0) ),
% 6.71/1.48      inference(renaming,[status(thm)],[c_540]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_610,plain,
% 6.71/1.48      ( ~ sP0(X0,X1,X2,X3,X4)
% 6.71/1.48      | v5_pre_topc(X2,k1_tsep_1(X4,X3,X1),X0)
% 6.71/1.48      | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))
% 6.71/1.48      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X6))))
% 6.71/1.48      | ~ v2_pre_topc(X6)
% 6.71/1.48      | ~ l1_pre_topc(X6)
% 6.71/1.48      | v2_struct_0(X6)
% 6.71/1.48      | ~ v1_funct_1(X5)
% 6.71/1.48      | X5 != X2
% 6.71/1.48      | X6 != X0
% 6.71/1.48      | sK5 != X1
% 6.71/1.48      | sK4 != X3
% 6.71/1.48      | sK2 != X4 ),
% 6.71/1.48      inference(resolution_lifted,[status(thm)],[c_9,c_541]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_611,plain,
% 6.71/1.48      ( ~ sP0(X0,sK5,X1,sK4,sK2)
% 6.71/1.48      | v5_pre_topc(X1,k1_tsep_1(sK2,sK4,sK5),X0)
% 6.71/1.48      | ~ v1_funct_2(X1,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))
% 6.71/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0))))
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | ~ v1_funct_1(X1) ),
% 6.71/1.48      inference(unflattening,[status(thm)],[c_610]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_855,plain,
% 6.71/1.48      ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 6.71/1.48      | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),X5,X3)
% 6.71/1.48      | ~ v5_pre_topc(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),X4,X3)
% 6.71/1.48      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),u1_struct_0(X5),u1_struct_0(X3))
% 6.71/1.48      | ~ v1_funct_2(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),u1_struct_0(X4),u1_struct_0(X3))
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
% 6.71/1.48      | ~ m1_subset_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | ~ v1_funct_1(X0)
% 6.71/1.48      | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X5,X6))
% 6.71/1.48      | ~ v1_funct_1(k3_tmap_1(X2,X3,k1_tsep_1(X2,X4,X5),X4,X6))
% 6.71/1.48      | X0 != X6
% 6.71/1.48      | X1 != X3
% 6.71/1.48      | sK5 != X5
% 6.71/1.48      | sK4 != X4
% 6.71/1.48      | sK2 != X2 ),
% 6.71/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_611]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_856,plain,
% 6.71/1.48      ( v5_pre_topc(X0,k1_tsep_1(sK2,sK4,sK5),X1)
% 6.71/1.48      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),sK5,X1)
% 6.71/1.48      | ~ v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),sK4,X1)
% 6.71/1.48      | ~ v1_funct_2(X0,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),u1_struct_0(sK5),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),u1_struct_0(sK4),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | ~ v1_funct_1(X0)
% 6.71/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK5,X0))
% 6.71/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,sK4,sK5),sK4,X0)) ),
% 6.71/1.48      inference(unflattening,[status(thm)],[c_855]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1505,plain,
% 6.71/1.48      ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55)
% 6.71/1.48      | ~ v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK5,X0_55)
% 6.71/1.48      | ~ v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK4,X0_55)
% 6.71/1.48      | ~ v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))
% 6.71/1.48      | ~ v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55))
% 6.71/1.48      | ~ v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55))
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55))))
% 6.71/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
% 6.71/1.48      | ~ m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
% 6.71/1.48      | ~ v2_pre_topc(X0_55)
% 6.71/1.48      | ~ l1_pre_topc(X0_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54))
% 6.71/1.48      | ~ v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_856]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2300,plain,
% 6.71/1.48      ( v5_pre_topc(X0_54,k1_tsep_1(sK2,sK4,sK5),X0_55) = iProver_top
% 6.71/1.48      | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),sK5,X0_55) != iProver_top
% 6.71/1.48      | v5_pre_topc(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),sK4,X0_55) != iProver_top
% 6.71/1.48      | v1_funct_2(X0_54,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)) != iProver_top
% 6.71/1.48      | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),u1_struct_0(sK5),u1_struct_0(X0_55)) != iProver_top
% 6.71/1.48      | v1_funct_2(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),u1_struct_0(sK4),u1_struct_0(X0_55)) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55)))) != iProver_top
% 6.71/1.48      | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55)))) != iProver_top
% 6.71/1.48      | m1_subset_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | v2_struct_0(X0_55) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK5,X0_54)) != iProver_top
% 6.71/1.48      | v1_funct_1(k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,X0_54)) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_1505]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_10742,plain,
% 6.71/1.48      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 6.71/1.48      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK5,sK3) != iProver_top
% 6.71/1.48      | v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK4,sK3) != iProver_top
% 6.71/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 6.71/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top
% 6.71/1.48      | v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7))) != iProver_top ),
% 6.71/1.48      inference(superposition,[status(thm)],[c_10731,c_2300]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_24,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
% 6.71/1.48      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
% 6.71/1.48      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 6.71/1.48      | r1_tsep_1(X0,X3)
% 6.71/1.48      | ~ m1_pre_topc(X3,X2)
% 6.71/1.48      | ~ m1_pre_topc(X0,X2)
% 6.71/1.48      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(X3)
% 6.71/1.48      | ~ v1_funct_1(X5)
% 6.71/1.48      | ~ v1_funct_1(X4) ),
% 6.71/1.48      inference(cnf_transformation,[],[f71]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_783,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k3_tmap_1(X2,X1,k1_tsep_1(X2,X0,X3),X0,k10_tmap_1(X2,X1,X0,X3,X4,X5)),X4)
% 6.71/1.48      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X2,X0,X3)),u1_struct_0(X1),k3_tmap_1(X2,X1,X0,k2_tsep_1(X2,X0,X3),X4),k3_tmap_1(X2,X1,X3,k2_tsep_1(X2,X0,X3),X5))
% 6.71/1.48      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(X0,X2)
% 6.71/1.48      | ~ m1_pre_topc(X3,X2)
% 6.71/1.48      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X2)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X2)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X3)
% 6.71/1.48      | v2_struct_0(X2)
% 6.71/1.48      | ~ v1_funct_1(X5)
% 6.71/1.48      | ~ v1_funct_1(X4)
% 6.71/1.48      | sK5 != X3
% 6.71/1.48      | sK4 != X0 ),
% 6.71/1.48      inference(resolution_lifted,[status(thm)],[c_24,c_40]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_784,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0)
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(sK5)
% 6.71/1.48      | v2_struct_0(sK4)
% 6.71/1.48      | ~ v1_funct_1(X3)
% 6.71/1.48      | ~ v1_funct_1(X2) ),
% 6.71/1.48      inference(unflattening,[status(thm)],[c_783]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_788,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0)
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | ~ v1_funct_1(X3)
% 6.71/1.48      | ~ v1_funct_1(X2) ),
% 6.71/1.48      inference(global_propositional_subsumption,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_784,c_44,c_42]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_789,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,sK4,sK5)),u1_struct_0(X1),k3_tmap_1(X0,X1,sK4,k2_tsep_1(X0,sK4,sK5),X2),k3_tmap_1(X0,X1,sK5,k2_tsep_1(X0,sK4,sK5),X3))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1),k3_tmap_1(X0,X1,k1_tsep_1(X0,sK4,sK5),sK4,k10_tmap_1(X0,X1,sK4,sK5,X2,X3)),X2)
% 6.71/1.48      | ~ v1_funct_2(X3,u1_struct_0(sK5),u1_struct_0(X1))
% 6.71/1.48      | ~ v1_funct_2(X2,u1_struct_0(sK4),u1_struct_0(X1))
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0)
% 6.71/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1))))
% 6.71/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1))))
% 6.71/1.48      | ~ v2_pre_topc(X1)
% 6.71/1.48      | ~ v2_pre_topc(X0)
% 6.71/1.48      | ~ l1_pre_topc(X1)
% 6.71/1.48      | ~ l1_pre_topc(X0)
% 6.71/1.48      | v2_struct_0(X0)
% 6.71/1.48      | v2_struct_0(X1)
% 6.71/1.48      | ~ v1_funct_1(X2)
% 6.71/1.48      | ~ v1_funct_1(X3) ),
% 6.71/1.48      inference(renaming,[status(thm)],[c_788]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_1506,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,sK4,k2_tsep_1(X0_55,sK4,sK5),X0_54),k3_tmap_1(X0_55,X1_55,sK5,k2_tsep_1(X0_55,sK4,sK5),X1_54))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54)),X0_54)
% 6.71/1.48      | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55))
% 6.71/1.48      | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55))
% 6.71/1.48      | ~ m1_pre_topc(sK5,X0_55)
% 6.71/1.48      | ~ m1_pre_topc(sK4,X0_55)
% 6.71/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55))))
% 6.71/1.48      | ~ v2_pre_topc(X1_55)
% 6.71/1.48      | ~ v2_pre_topc(X0_55)
% 6.71/1.48      | ~ l1_pre_topc(X1_55)
% 6.71/1.48      | ~ l1_pre_topc(X0_55)
% 6.71/1.48      | v2_struct_0(X1_55)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(X1_54) ),
% 6.71/1.48      inference(subtyping,[status(esa)],[c_789]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2299,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(X0_55,sK4,sK5)),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,sK4,k2_tsep_1(X0_55,sK4,sK5),X0_54),k3_tmap_1(X0_55,X1_55,sK5,k2_tsep_1(X0_55,sK4,sK5),X1_54)) != iProver_top
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X1_55),k3_tmap_1(X0_55,X1_55,k1_tsep_1(X0_55,sK4,sK5),sK4,k10_tmap_1(X0_55,X1_55,sK4,sK5,X0_54,X1_54)),X0_54) = iProver_top
% 6.71/1.48      | v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X1_55)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,X0_55) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,X0_55) != iProver_top
% 6.71/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X1_55)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | v2_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X1_55) != iProver_top
% 6.71/1.48      | l1_pre_topc(X0_55) != iProver_top
% 6.71/1.48      | v2_struct_0(X1_55) = iProver_top
% 6.71/1.48      | v2_struct_0(X0_55) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(X1_54) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_1506]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_6695,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(superposition,[status(thm)],[c_2278,c_2299]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_2945,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,X0_55,sK5,k2_tsep_1(sK2,sK4,sK5),X1_54))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(X0_55),k3_tmap_1(sK2,X0_55,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,X0_55,sK4,sK5,X0_54,X1_54)),X0_54)
% 6.71/1.48      | ~ v1_funct_2(X1_54,u1_struct_0(sK5),u1_struct_0(X0_55))
% 6.71/1.48      | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(X0_55))
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(X0_55))))
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(X0_55))))
% 6.71/1.48      | ~ v2_pre_topc(X0_55)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(X0_55)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(X0_55)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(X1_54) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_1506]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3313,plain,
% 6.71/1.48      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7))
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),X0_54)
% 6.71/1.48      | ~ v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3))
% 6.71/1.48      | ~ v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_pre_topc(sK5,sK2)
% 6.71/1.48      | ~ m1_pre_topc(sK4,sK2)
% 6.71/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
% 6.71/1.48      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v2_pre_topc(sK3)
% 6.71/1.48      | ~ v2_pre_topc(sK2)
% 6.71/1.48      | ~ l1_pre_topc(sK3)
% 6.71/1.48      | ~ l1_pre_topc(sK2)
% 6.71/1.48      | v2_struct_0(sK3)
% 6.71/1.48      | v2_struct_0(sK2)
% 6.71/1.48      | ~ v1_funct_1(X0_54)
% 6.71/1.48      | ~ v1_funct_1(sK7) ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_2945]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3314,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),X0_54),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,X0_54,sK7)),X0_54) = iProver_top
% 6.71/1.48      | v1_funct_2(X0_54,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(X0_54) != iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_3313]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_3316,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(k2_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,sK4,k2_tsep_1(sK2,sK4,sK5),sK6),k3_tmap_1(sK2,sK3,sK5,k2_tsep_1(sK2,sK4,sK5),sK7)) != iProver_top
% 6.71/1.48      | r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK5,sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(instantiation,[status(thm)],[c_3314]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_6698,plain,
% 6.71/1.48      ( r2_funct_2(u1_struct_0(sK4),u1_struct_0(sK3),k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)),sK6) = iProver_top ),
% 6.71/1.48      inference(global_propositional_subsumption,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_6695,c_51,c_52,c_53,c_54,c_55,c_56,c_58,c_60,c_62,
% 6.71/1.48                 c_63,c_65,c_66,c_67,c_69,c_70,c_3316]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_9470,plain,
% 6.71/1.48      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6
% 6.71/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_pre_topc(k1_tsep_1(sK2,sK4,sK5),sK2) != iProver_top
% 6.71/1.48      | m1_pre_topc(sK4,sK2) != iProver_top
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK2) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK2) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v2_struct_0(sK2) = iProver_top
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(superposition,[status(thm)],[c_6698,c_9465]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_9789,plain,
% 6.71/1.48      ( k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) = sK6 ),
% 6.71/1.48      inference(global_propositional_subsumption,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_9470,c_51,c_52,c_53,c_54,c_55,c_56,c_57,c_58,c_59,
% 6.71/1.48                 c_60,c_62,c_63,c_65,c_66,c_67,c_69,c_3703,c_3811,c_3841,
% 6.71/1.48                 c_3949,c_6667]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_10841,plain,
% 6.71/1.48      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) = iProver_top
% 6.71/1.48      | v5_pre_topc(sK7,sK5,sK3) != iProver_top
% 6.71/1.48      | v5_pre_topc(sK6,sK4,sK3) != iProver_top
% 6.71/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK7,u1_struct_0(sK5),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | v1_funct_2(sK6,u1_struct_0(sK4),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v2_pre_topc(sK3) != iProver_top
% 6.71/1.48      | l1_pre_topc(sK3) != iProver_top
% 6.71/1.48      | v2_struct_0(sK3) = iProver_top
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top
% 6.71/1.48      | v1_funct_1(sK7) != iProver_top
% 6.71/1.48      | v1_funct_1(sK6) != iProver_top ),
% 6.71/1.48      inference(light_normalisation,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_10742,c_9789,c_10731]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_29,negated_conjecture,
% 6.71/1.48      ( ~ v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3)
% 6.71/1.48      | ~ v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))
% 6.71/1.48      | ~ m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))
% 6.71/1.48      | ~ v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
% 6.71/1.48      inference(cnf_transformation,[],[f97]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_72,plain,
% 6.71/1.48      ( v5_pre_topc(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_tsep_1(sK2,sK4,sK5),sK3) != iProver_top
% 6.71/1.48      | v1_funct_2(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) != iProver_top
% 6.71/1.48      | m1_subset_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) != iProver_top
% 6.71/1.48      | v1_funct_1(k10_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7)) != iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_33,negated_conjecture,
% 6.71/1.48      ( v5_pre_topc(sK7,sK5,sK3) ),
% 6.71/1.48      inference(cnf_transformation,[],[f93]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_68,plain,
% 6.71/1.48      ( v5_pre_topc(sK7,sK5,sK3) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_37,negated_conjecture,
% 6.71/1.48      ( v5_pre_topc(sK6,sK4,sK3) ),
% 6.71/1.48      inference(cnf_transformation,[],[f89]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(c_64,plain,
% 6.71/1.48      ( v5_pre_topc(sK6,sK4,sK3) = iProver_top ),
% 6.71/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.71/1.48  
% 6.71/1.48  cnf(contradiction,plain,
% 6.71/1.48      ( $false ),
% 6.71/1.48      inference(minisat,
% 6.71/1.48                [status(thm)],
% 6.71/1.48                [c_10841,c_3949,c_3841,c_3811,c_72,c_69,c_68,c_67,c_66,
% 6.71/1.48                 c_65,c_64,c_63,c_62,c_60,c_59,c_58,c_57,c_56,c_55,c_54,
% 6.71/1.48                 c_53,c_52,c_51]) ).
% 6.71/1.48  
% 6.71/1.48  
% 6.71/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.71/1.48  
% 6.71/1.48  ------                               Statistics
% 6.71/1.48  
% 6.71/1.48  ------ General
% 6.71/1.48  
% 6.71/1.48  abstr_ref_over_cycles:                  0
% 6.71/1.48  abstr_ref_under_cycles:                 0
% 6.71/1.48  gc_basic_clause_elim:                   0
% 6.71/1.48  forced_gc_time:                         0
% 6.71/1.48  parsing_time:                           0.012
% 6.71/1.48  unif_index_cands_time:                  0.
% 6.71/1.48  unif_index_add_time:                    0.
% 6.71/1.48  orderings_time:                         0.
% 6.71/1.48  out_proof_time:                         0.029
% 6.71/1.48  total_time:                             0.622
% 6.71/1.48  num_of_symbols:                         59
% 6.71/1.48  num_of_terms:                           10617
% 6.71/1.48  
% 6.71/1.48  ------ Preprocessing
% 6.71/1.48  
% 6.71/1.48  num_of_splits:                          0
% 6.71/1.48  num_of_split_atoms:                     0
% 6.71/1.48  num_of_reused_defs:                     0
% 6.71/1.48  num_eq_ax_congr_red:                    40
% 6.71/1.48  num_of_sem_filtered_clauses:            1
% 6.71/1.48  num_of_subtypes:                        5
% 6.71/1.48  monotx_restored_types:                  0
% 6.71/1.48  sat_num_of_epr_types:                   0
% 6.71/1.48  sat_num_of_non_cyclic_types:            0
% 6.71/1.48  sat_guarded_non_collapsed_types:        1
% 6.71/1.48  num_pure_diseq_elim:                    0
% 6.71/1.48  simp_replaced_by:                       0
% 6.71/1.48  res_preprocessed:                       199
% 6.71/1.48  prep_upred:                             0
% 6.71/1.48  prep_unflattend:                        79
% 6.71/1.48  smt_new_axioms:                         0
% 6.71/1.48  pred_elim_cands:                        9
% 6.71/1.48  pred_elim:                              4
% 6.71/1.48  pred_elim_cl:                           8
% 6.71/1.48  pred_elim_cycles:                       6
% 6.71/1.48  merged_defs:                            0
% 6.71/1.48  merged_defs_ncl:                        0
% 6.71/1.48  bin_hyper_res:                          0
% 6.71/1.48  prep_cycles:                            4
% 6.71/1.48  pred_elim_time:                         0.036
% 6.71/1.48  splitting_time:                         0.
% 6.71/1.48  sem_filter_time:                        0.
% 6.71/1.48  monotx_time:                            0.
% 6.71/1.48  subtype_inf_time:                       0.001
% 6.71/1.48  
% 6.71/1.48  ------ Problem properties
% 6.71/1.48  
% 6.71/1.48  clauses:                                43
% 6.71/1.48  conjectures:                            20
% 6.71/1.48  epr:                                    16
% 6.71/1.48  horn:                                   24
% 6.71/1.48  ground:                                 20
% 6.71/1.48  unary:                                  19
% 6.71/1.48  binary:                                 1
% 6.71/1.48  lits:                                   269
% 6.71/1.48  lits_eq:                                1
% 6.71/1.48  fd_pure:                                0
% 6.71/1.48  fd_pseudo:                              0
% 6.71/1.48  fd_cond:                                0
% 6.71/1.48  fd_pseudo_cond:                         1
% 6.71/1.48  ac_symbols:                             0
% 6.71/1.48  
% 6.71/1.48  ------ Propositional Solver
% 6.71/1.48  
% 6.71/1.48  prop_solver_calls:                      30
% 6.71/1.48  prop_fast_solver_calls:                 3849
% 6.71/1.48  smt_solver_calls:                       0
% 6.71/1.48  smt_fast_solver_calls:                  0
% 6.71/1.48  prop_num_of_clauses:                    3271
% 6.71/1.48  prop_preprocess_simplified:             9890
% 6.71/1.48  prop_fo_subsumed:                       216
% 6.71/1.48  prop_solver_time:                       0.
% 6.71/1.48  smt_solver_time:                        0.
% 6.71/1.48  smt_fast_solver_time:                   0.
% 6.71/1.48  prop_fast_solver_time:                  0.
% 6.71/1.48  prop_unsat_core_time:                   0.
% 6.71/1.48  
% 6.71/1.48  ------ QBF
% 6.71/1.48  
% 6.71/1.48  qbf_q_res:                              0
% 6.71/1.48  qbf_num_tautologies:                    0
% 6.71/1.48  qbf_prep_cycles:                        0
% 6.71/1.48  
% 6.71/1.48  ------ BMC1
% 6.71/1.48  
% 6.71/1.48  bmc1_current_bound:                     -1
% 6.71/1.48  bmc1_last_solved_bound:                 -1
% 6.71/1.48  bmc1_unsat_core_size:                   -1
% 6.71/1.48  bmc1_unsat_core_parents_size:           -1
% 6.71/1.48  bmc1_merge_next_fun:                    0
% 6.71/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.71/1.48  
% 6.71/1.48  ------ Instantiation
% 6.71/1.48  
% 6.71/1.48  inst_num_of_clauses:                    923
% 6.71/1.48  inst_num_in_passive:                    450
% 6.71/1.48  inst_num_in_active:                     446
% 6.71/1.48  inst_num_in_unprocessed:                27
% 6.71/1.48  inst_num_of_loops:                      470
% 6.71/1.48  inst_num_of_learning_restarts:          0
% 6.71/1.48  inst_num_moves_active_passive:          20
% 6.71/1.48  inst_lit_activity:                      0
% 6.71/1.48  inst_lit_activity_moves:                0
% 6.71/1.48  inst_num_tautologies:                   0
% 6.71/1.48  inst_num_prop_implied:                  0
% 6.71/1.48  inst_num_existing_simplified:           0
% 6.71/1.48  inst_num_eq_res_simplified:             0
% 6.71/1.48  inst_num_child_elim:                    0
% 6.71/1.48  inst_num_of_dismatching_blockings:      119
% 6.71/1.48  inst_num_of_non_proper_insts:           794
% 6.71/1.48  inst_num_of_duplicates:                 0
% 6.71/1.48  inst_inst_num_from_inst_to_res:         0
% 6.71/1.48  inst_dismatching_checking_time:         0.
% 6.71/1.48  
% 6.71/1.48  ------ Resolution
% 6.71/1.48  
% 6.71/1.48  res_num_of_clauses:                     0
% 6.71/1.48  res_num_in_passive:                     0
% 6.71/1.48  res_num_in_active:                      0
% 6.71/1.48  res_num_of_loops:                       203
% 6.71/1.48  res_forward_subset_subsumed:            40
% 6.71/1.48  res_backward_subset_subsumed:           0
% 6.71/1.48  res_forward_subsumed:                   0
% 6.71/1.48  res_backward_subsumed:                  0
% 6.71/1.48  res_forward_subsumption_resolution:     0
% 6.71/1.48  res_backward_subsumption_resolution:    0
% 6.71/1.48  res_clause_to_clause_subsumption:       1286
% 6.71/1.48  res_orphan_elimination:                 0
% 6.71/1.48  res_tautology_del:                      85
% 6.71/1.48  res_num_eq_res_simplified:              0
% 6.71/1.48  res_num_sel_changes:                    0
% 6.71/1.48  res_moves_from_active_to_pass:          0
% 6.71/1.48  
% 6.71/1.48  ------ Superposition
% 6.71/1.48  
% 6.71/1.48  sup_time_total:                         0.
% 6.71/1.48  sup_time_generating:                    0.
% 6.71/1.48  sup_time_sim_full:                      0.
% 6.71/1.48  sup_time_sim_immed:                     0.
% 6.71/1.48  
% 6.71/1.48  sup_num_of_clauses:                     105
% 6.71/1.48  sup_num_in_active:                      89
% 6.71/1.48  sup_num_in_passive:                     16
% 6.71/1.48  sup_num_of_loops:                       92
% 6.71/1.48  sup_fw_superposition:                   50
% 6.71/1.48  sup_bw_superposition:                   74
% 6.71/1.48  sup_immediate_simplified:               45
% 6.71/1.48  sup_given_eliminated:                   0
% 6.71/1.48  comparisons_done:                       0
% 6.71/1.48  comparisons_avoided:                    0
% 6.71/1.48  
% 6.71/1.48  ------ Simplifications
% 6.71/1.48  
% 6.71/1.48  
% 6.71/1.48  sim_fw_subset_subsumed:                 32
% 6.71/1.48  sim_bw_subset_subsumed:                 2
% 6.71/1.48  sim_fw_subsumed:                        11
% 6.71/1.48  sim_bw_subsumed:                        0
% 6.71/1.48  sim_fw_subsumption_res:                 11
% 6.71/1.48  sim_bw_subsumption_res:                 0
% 6.71/1.48  sim_tautology_del:                      4
% 6.71/1.48  sim_eq_tautology_del:                   9
% 6.71/1.48  sim_eq_res_simp:                        0
% 6.71/1.48  sim_fw_demodulated:                     2
% 6.71/1.48  sim_bw_demodulated:                     2
% 6.71/1.48  sim_light_normalised:                   5
% 6.71/1.48  sim_joinable_taut:                      0
% 6.71/1.48  sim_joinable_simp:                      0
% 6.71/1.48  sim_ac_normalised:                      0
% 6.71/1.48  sim_smt_subsumption:                    0
% 6.71/1.48  
%------------------------------------------------------------------------------
