%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1830+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:33 EST 2020

% Result     : Theorem 4.53s
% Output     : Refutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 938 expanded)
%              Number of leaves         :   10 ( 537 expanded)
%              Depth                    :    7
%              Number of atoms          :  635 (26752 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   29 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5153,plain,(
    $false ),
    inference(global_subsumption,[],[f3865,f3863,f3862,f3861,f3860,f3859,f3858,f3857,f3856,f3855,f3854,f3852,f3851,f3849,f3848,f3847,f3846,f3845,f3844,f3843,f4786,f5100,f5096,f5092,f5140])).

fof(f5140,plain,
    ( ~ r4_tsep_1(sK12,sK14,sK15)
    | v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),k1_tsep_1(sK12,sK14,sK15),sK13)
    | ~ m1_subset_1(sK17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
    | ~ v5_pre_topc(sK17,sK15,sK13)
    | ~ v1_funct_2(sK17,u1_struct_0(sK15),u1_struct_0(sK13))
    | ~ v1_funct_1(sK17)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13))))
    | ~ v5_pre_topc(sK16,sK14,sK13)
    | ~ v1_funct_2(sK16,u1_struct_0(sK14),u1_struct_0(sK13))
    | ~ v1_funct_1(sK16)
    | r1_tsep_1(sK14,sK15)
    | ~ m1_pre_topc(sK15,sK12)
    | v2_struct_0(sK15)
    | ~ m1_pre_topc(sK14,sK12)
    | v2_struct_0(sK14)
    | ~ l1_pre_topc(sK13)
    | ~ v2_pre_topc(sK13)
    | v2_struct_0(sK13)
    | ~ l1_pre_topc(sK12)
    | ~ v2_pre_topc(sK12)
    | v2_struct_0(sK12) ),
    inference(resolution,[],[f3864,f3927])).

fof(f3927,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
      | ~ r4_tsep_1(X0,X2,X3)
      | v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X5,X3,X1)
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(cnf_transformation,[],[f3577])).

fof(f3577,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(flattening,[],[f3576])).

fof(f3576,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
                          | ~ r4_tsep_1(X0,X2,X3)
                          | ~ r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X5,X3,X1)
                          | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X4,X2,X1)
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
    inference(ennf_transformation,[],[f3423])).

fof(f3423,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).

fof(f3864,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,sK15),sK16),k3_tmap_1(sK12,sK13,sK15,k2_tsep_1(sK12,sK14,sK15),sK17)) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3754,plain,
    ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))))
      | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),k1_tsep_1(sK12,sK14,sK15),sK13)
      | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))
      | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17)) )
    & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,sK15),sK16),k3_tmap_1(sK12,sK13,sK15,k2_tsep_1(sK12,sK14,sK15),sK17))
    & m1_subset_1(sK17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
    & v5_pre_topc(sK17,sK15,sK13)
    & v1_funct_2(sK17,u1_struct_0(sK15),u1_struct_0(sK13))
    & v1_funct_1(sK17)
    & m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13))))
    & v5_pre_topc(sK16,sK14,sK13)
    & v1_funct_2(sK16,u1_struct_0(sK14),u1_struct_0(sK13))
    & v1_funct_1(sK16)
    & ~ r1_tsep_1(sK14,sK15)
    & m1_pre_topc(sK15,sK12)
    & v1_borsuk_1(sK15,sK12)
    & ~ v2_struct_0(sK15)
    & m1_pre_topc(sK14,sK12)
    & v1_borsuk_1(sK14,sK12)
    & ~ v2_struct_0(sK14)
    & l1_pre_topc(sK13)
    & v2_pre_topc(sK13)
    & ~ v2_struct_0(sK13)
    & l1_pre_topc(sK12)
    & v2_pre_topc(sK12)
    & ~ v2_struct_0(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14,sK15,sK16,sK17])],[f3537,f3753,f3752,f3751,f3750,f3749,f3748])).

fof(f3748,plain,
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
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
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
                          ( ( ~ m1_subset_1(k10_tmap_1(sK12,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,X2,X3)),u1_struct_0(X1))))
                            | ~ v5_pre_topc(k10_tmap_1(sK12,X1,X2,X3,X4,X5),k1_tsep_1(sK12,X2,X3),X1)
                            | ~ v1_funct_2(k10_tmap_1(sK12,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK12,X2,X3)),u1_struct_0(X1))
                            | ~ v1_funct_1(k10_tmap_1(sK12,X1,X2,X3,X4,X5)) )
                          & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK12,X1,X2,k2_tsep_1(sK12,X2,X3),X4),k3_tmap_1(sK12,X1,X3,k2_tsep_1(sK12,X2,X3),X5))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(X5,X3,X1)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & ~ r1_tsep_1(X2,X3)
                  & m1_pre_topc(X3,sK12)
                  & v1_borsuk_1(X3,sK12)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK12)
              & v1_borsuk_1(X2,sK12)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK12)
      & v2_pre_topc(sK12)
      & ~ v2_struct_0(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f3749,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ~ m1_subset_1(k10_tmap_1(sK12,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,X2,X3)),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k10_tmap_1(sK12,X1,X2,X3,X4,X5),k1_tsep_1(sK12,X2,X3),X1)
                          | ~ v1_funct_2(k10_tmap_1(sK12,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK12,X2,X3)),u1_struct_0(X1))
                          | ~ v1_funct_1(k10_tmap_1(sK12,X1,X2,X3,X4,X5)) )
                        & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,X2,X3)),u1_struct_0(X1),k3_tmap_1(sK12,X1,X2,k2_tsep_1(sK12,X2,X3),X4),k3_tmap_1(sK12,X1,X3,k2_tsep_1(sK12,X2,X3),X5))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(X5,X3,X1)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & ~ r1_tsep_1(X2,X3)
                & m1_pre_topc(X3,sK12)
                & v1_borsuk_1(X3,sK12)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK12)
            & v1_borsuk_1(X2,sK12)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,X2,X3)),u1_struct_0(sK13))))
                        | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,X2,X3,X4,X5),k1_tsep_1(sK12,X2,X3),sK13)
                        | ~ v1_funct_2(k10_tmap_1(sK12,sK13,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK12,X2,X3)),u1_struct_0(sK13))
                        | ~ v1_funct_1(k10_tmap_1(sK12,sK13,X2,X3,X4,X5)) )
                      & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,X2,X3)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,X2,k2_tsep_1(sK12,X2,X3),X4),k3_tmap_1(sK12,sK13,X3,k2_tsep_1(sK12,X2,X3),X5))
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK13))))
                      & v5_pre_topc(X5,X3,sK13)
                      & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK13))
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK13))))
                  & v5_pre_topc(X4,X2,sK13)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK13))
                  & v1_funct_1(X4) )
              & ~ r1_tsep_1(X2,X3)
              & m1_pre_topc(X3,sK12)
              & v1_borsuk_1(X3,sK12)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK12)
          & v1_borsuk_1(X2,sK12)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK13)
      & v2_pre_topc(sK13)
      & ~ v2_struct_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f3750,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,X2,X3)),u1_struct_0(sK13))))
                      | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,X2,X3,X4,X5),k1_tsep_1(sK12,X2,X3),sK13)
                      | ~ v1_funct_2(k10_tmap_1(sK12,sK13,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(sK12,X2,X3)),u1_struct_0(sK13))
                      | ~ v1_funct_1(k10_tmap_1(sK12,sK13,X2,X3,X4,X5)) )
                    & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,X2,X3)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,X2,k2_tsep_1(sK12,X2,X3),X4),k3_tmap_1(sK12,sK13,X3,k2_tsep_1(sK12,X2,X3),X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK13))))
                    & v5_pre_topc(X5,X3,sK13)
                    & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK13))
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK13))))
                & v5_pre_topc(X4,X2,sK13)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK13))
                & v1_funct_1(X4) )
            & ~ r1_tsep_1(X2,X3)
            & m1_pre_topc(X3,sK12)
            & v1_borsuk_1(X3,sK12)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK12)
        & v1_borsuk_1(X2,sK12)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,X3)),u1_struct_0(sK13))))
                    | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,X3,X4,X5),k1_tsep_1(sK12,sK14,X3),sK13)
                    | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,X3,X4,X5),u1_struct_0(k1_tsep_1(sK12,sK14,X3)),u1_struct_0(sK13))
                    | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,X3,X4,X5)) )
                  & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,X3)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,X3),X4),k3_tmap_1(sK12,sK13,X3,k2_tsep_1(sK12,sK14,X3),X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK13))))
                  & v5_pre_topc(X5,X3,sK13)
                  & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK13))
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13))))
              & v5_pre_topc(X4,sK14,sK13)
              & v1_funct_2(X4,u1_struct_0(sK14),u1_struct_0(sK13))
              & v1_funct_1(X4) )
          & ~ r1_tsep_1(sK14,X3)
          & m1_pre_topc(X3,sK12)
          & v1_borsuk_1(X3,sK12)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK14,sK12)
      & v1_borsuk_1(sK14,sK12)
      & ~ v2_struct_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f3751,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,X3)),u1_struct_0(sK13))))
                  | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,X3,X4,X5),k1_tsep_1(sK12,sK14,X3),sK13)
                  | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,X3,X4,X5),u1_struct_0(k1_tsep_1(sK12,sK14,X3)),u1_struct_0(sK13))
                  | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,X3,X4,X5)) )
                & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,X3)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,X3),X4),k3_tmap_1(sK12,sK13,X3,k2_tsep_1(sK12,sK14,X3),X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK13))))
                & v5_pre_topc(X5,X3,sK13)
                & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(sK13))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13))))
            & v5_pre_topc(X4,sK14,sK13)
            & v1_funct_2(X4,u1_struct_0(sK14),u1_struct_0(sK13))
            & v1_funct_1(X4) )
        & ~ r1_tsep_1(sK14,X3)
        & m1_pre_topc(X3,sK12)
        & v1_borsuk_1(X3,sK12)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,sK15,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))))
                | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,sK15,X4,X5),k1_tsep_1(sK12,sK14,sK15),sK13)
                | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,sK15,X4,X5),u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))
                | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,sK15,X4,X5)) )
              & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,sK15),X4),k3_tmap_1(sK12,sK13,sK15,k2_tsep_1(sK12,sK14,sK15),X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
              & v5_pre_topc(X5,sK15,sK13)
              & v1_funct_2(X5,u1_struct_0(sK15),u1_struct_0(sK13))
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13))))
          & v5_pre_topc(X4,sK14,sK13)
          & v1_funct_2(X4,u1_struct_0(sK14),u1_struct_0(sK13))
          & v1_funct_1(X4) )
      & ~ r1_tsep_1(sK14,sK15)
      & m1_pre_topc(sK15,sK12)
      & v1_borsuk_1(sK15,sK12)
      & ~ v2_struct_0(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f3752,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,sK15,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))))
              | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,sK15,X4,X5),k1_tsep_1(sK12,sK14,sK15),sK13)
              | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,sK15,X4,X5),u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))
              | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,sK15,X4,X5)) )
            & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,sK15),X4),k3_tmap_1(sK12,sK13,sK15,k2_tsep_1(sK12,sK14,sK15),X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
            & v5_pre_topc(X5,sK15,sK13)
            & v1_funct_2(X5,u1_struct_0(sK15),u1_struct_0(sK13))
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13))))
        & v5_pre_topc(X4,sK14,sK13)
        & v1_funct_2(X4,u1_struct_0(sK14),u1_struct_0(sK13))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))))
            | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,X5),k1_tsep_1(sK12,sK14,sK15),sK13)
            | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,X5),u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))
            | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,X5)) )
          & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,sK15),sK16),k3_tmap_1(sK12,sK13,sK15,k2_tsep_1(sK12,sK14,sK15),X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
          & v5_pre_topc(X5,sK15,sK13)
          & v1_funct_2(X5,u1_struct_0(sK15),u1_struct_0(sK13))
          & v1_funct_1(X5) )
      & m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13))))
      & v5_pre_topc(sK16,sK14,sK13)
      & v1_funct_2(sK16,u1_struct_0(sK14),u1_struct_0(sK13))
      & v1_funct_1(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f3753,plain,
    ( ? [X5] :
        ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))))
          | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,X5),k1_tsep_1(sK12,sK14,sK15),sK13)
          | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,X5),u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))
          | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,X5)) )
        & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,sK15),sK16),k3_tmap_1(sK12,sK13,sK15,k2_tsep_1(sK12,sK14,sK15),X5))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
        & v5_pre_topc(X5,sK15,sK13)
        & v1_funct_2(X5,u1_struct_0(sK15),u1_struct_0(sK13))
        & v1_funct_1(X5) )
   => ( ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))))
        | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),k1_tsep_1(sK12,sK14,sK15),sK13)
        | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))
        | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17)) )
      & r2_funct_2(u1_struct_0(k2_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13),k3_tmap_1(sK12,sK13,sK14,k2_tsep_1(sK12,sK14,sK15),sK16),k3_tmap_1(sK12,sK13,sK15,k2_tsep_1(sK12,sK14,sK15),sK17))
      & m1_subset_1(sK17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13))))
      & v5_pre_topc(sK17,sK15,sK13)
      & v1_funct_2(sK17,u1_struct_0(sK15),u1_struct_0(sK13))
      & v1_funct_1(sK17) ) ),
    introduced(choice_axiom,[])).

fof(f3537,plain,(
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3536])).

fof(f3536,plain,(
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
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3426])).

fof(f3426,negated_conjecture,(
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
                  & v1_borsuk_1(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
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
                             => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                               => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                  & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                  & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                  & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3425])).

fof(f3425,conjecture,(
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
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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
                           => ( r2_funct_2(u1_struct_0(k2_tsep_1(X0,X2,X3)),u1_struct_0(X1),k3_tmap_1(X0,X1,X2,k2_tsep_1(X0,X2,X3),X4),k3_tmap_1(X0,X1,X3,k2_tsep_1(X0,X2,X3),X5))
                             => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                                & v5_pre_topc(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X2,X3),X1)
                                & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                                & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_tmap_1)).

fof(f5092,plain,(
    v1_funct_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17)) ),
    inference(unit_resulting_resolution,[],[f3843,f3844,f3845,f3846,f3847,f3848,f3849,f3852,f3851,f3854,f3856,f3860,f3857,f3859,f3861,f3863,f3895])).

fof(f3895,plain,(
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
    inference(cnf_transformation,[],[f3559])).

fof(f3559,plain,(
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
    inference(flattening,[],[f3558])).

fof(f3558,plain,(
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
    inference(ennf_transformation,[],[f3343])).

fof(f3343,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f5096,plain,(
    v1_funct_2(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13)) ),
    inference(unit_resulting_resolution,[],[f3843,f3844,f3845,f3846,f3847,f3848,f3849,f3852,f3851,f3854,f3856,f3860,f3857,f3859,f3861,f3863,f3896])).

fof(f3896,plain,(
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
    inference(cnf_transformation,[],[f3559])).

fof(f5100,plain,(
    m1_subset_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13)))) ),
    inference(unit_resulting_resolution,[],[f3843,f3844,f3845,f3846,f3847,f3848,f3849,f3852,f3851,f3854,f3856,f3860,f3857,f3859,f3861,f3863,f3897])).

fof(f3897,plain,(
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
    inference(cnf_transformation,[],[f3559])).

fof(f4786,plain,(
    r4_tsep_1(sK12,sK14,sK15) ),
    inference(unit_resulting_resolution,[],[f3843,f3844,f3845,f3850,f3851,f3853,f3854,f4111])).

fof(f4111,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r4_tsep_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f3717])).

fof(f3717,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3716])).

fof(f3716,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3520])).

fof(f3520,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

fof(f3853,plain,(
    v1_borsuk_1(sK15,sK12) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3850,plain,(
    v1_borsuk_1(sK14,sK12) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3843,plain,(
    ~ v2_struct_0(sK12) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3844,plain,(
    v2_pre_topc(sK12) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3845,plain,(
    l1_pre_topc(sK12) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3846,plain,(
    ~ v2_struct_0(sK13) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3847,plain,(
    v2_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3848,plain,(
    l1_pre_topc(sK13) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3849,plain,(
    ~ v2_struct_0(sK14) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3851,plain,(
    m1_pre_topc(sK14,sK12) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3852,plain,(
    ~ v2_struct_0(sK15) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3854,plain,(
    m1_pre_topc(sK15,sK12) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3855,plain,(
    ~ r1_tsep_1(sK14,sK15) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3856,plain,(
    v1_funct_1(sK16) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3857,plain,(
    v1_funct_2(sK16,u1_struct_0(sK14),u1_struct_0(sK13)) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3858,plain,(
    v5_pre_topc(sK16,sK14,sK13) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3859,plain,(
    m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK14),u1_struct_0(sK13)))) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3860,plain,(
    v1_funct_1(sK17) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3861,plain,(
    v1_funct_2(sK17,u1_struct_0(sK15),u1_struct_0(sK13)) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3862,plain,(
    v5_pre_topc(sK17,sK15,sK13) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3863,plain,(
    m1_subset_1(sK17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK15),u1_struct_0(sK13)))) ),
    inference(cnf_transformation,[],[f3754])).

fof(f3865,plain,
    ( ~ m1_subset_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))))
    | ~ v5_pre_topc(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),k1_tsep_1(sK12,sK14,sK15),sK13)
    | ~ v1_funct_2(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17),u1_struct_0(k1_tsep_1(sK12,sK14,sK15)),u1_struct_0(sK13))
    | ~ v1_funct_1(k10_tmap_1(sK12,sK13,sK14,sK15,sK16,sK17)) ),
    inference(cnf_transformation,[],[f3754])).
%------------------------------------------------------------------------------
