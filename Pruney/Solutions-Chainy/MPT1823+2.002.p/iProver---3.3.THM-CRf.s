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
% DateTime   : Thu Dec  3 12:24:22 EST 2020

% Result     : Theorem 51.48s
% Output     : CNFRefutation 51.48s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1530)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f11,conjecture,(
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
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
                   => ( k1_tsep_1(X0,X2,X3) = X0
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),sK4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,sK4,X2),k2_tmap_1(X0,X1,sK4,X3)))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & k1_tsep_1(X0,X2,X3) = X0
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,sK3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,sK3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,sK3)))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & k1_tsep_1(X0,X2,sK3) = X0
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & k1_tsep_1(X0,X2,X3) = X0
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,sK2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,sK2,X3,k2_tmap_1(X0,X1,X4,sK2),k2_tmap_1(X0,X1,X4,X3)))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & k1_tsep_1(X0,sK2,X3) = X0
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
                    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(X0,sK1,X2,X3,k2_tmap_1(X0,sK1,X4,X2),k2_tmap_1(X0,sK1,X4,X3)))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & k1_tsep_1(X0,X2,X3) = X0
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
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
                      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(sK0,X2,X3) = sK0
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & k1_tsep_1(sK0,sK2,sK3) = sK0
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f41,f40,f39,f38,f37])).

fof(f70,plain,(
    k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
      | ~ m1_pre_topc(X3,X2)
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
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
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
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
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
    inference(flattening,[],[f31])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
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
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f26])).

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

fof(f14,plain,(
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

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k10_tmap_1(X5,X2,X1,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_295,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_107494,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1))
    | ~ v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_pre_topc(X1_52,X2_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X2_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_52)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v1_funct_1(k10_tmap_1(X2_52,sK1,X0_52,X1_52,X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_125968,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_107494])).

cnf(c_21,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_284,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X1,X4,X0,X3),u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_296,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | v1_funct_2(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_912,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52)) = iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_4986,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_912])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5111,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4986,c_32,c_33,c_34,c_38,c_39,c_40,c_41])).

cnf(c_5112,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_5111])).

cnf(c_281,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_926,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_287,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_921,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_298,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_910,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_2563,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_910])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3171,plain,
    ( v2_struct_0(X1_52) = iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2563,c_35,c_36,c_37,c_42,c_43,c_44,c_1530])).

cnf(c_3172,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3171])).

cnf(c_3185,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_3172])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_299,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_909,plain,
    ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52)
    | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_2384,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_909])).

cnf(c_2389,plain,
    ( m1_pre_topc(X0_52,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2384,c_32,c_33,c_34,c_35,c_36,c_37,c_42,c_43])).

cnf(c_2390,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
    | m1_pre_topc(X0_52,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2389])).

cnf(c_2398,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_926,c_2390])).

cnf(c_3225,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3185,c_2398])).

cnf(c_307,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_351,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_294,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X2_52,X1_52)
    | m1_pre_topc(k1_tsep_1(X1_52,X2_52,X0_52),X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1467,plain,
    ( ~ m1_pre_topc(X0_52,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK2,X0_52),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_294])).

cnf(c_1578,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_1579,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1578])).

cnf(c_327,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_pre_topc(X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_1672,plain,
    ( m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | X0_52 != k1_tsep_1(sK0,sK2,sK3)
    | X1_52 != sK0 ),
    inference(instantiation,[status(thm)],[c_327])).

cnf(c_1673,plain,
    ( X0_52 != k1_tsep_1(sK0,sK2,sK3)
    | X1_52 != sK0
    | m1_pre_topc(X0_52,X1_52) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1672])).

cnf(c_1675,plain,
    ( sK0 != k1_tsep_1(sK0,sK2,sK3)
    | sK0 != sK0
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1673])).

cnf(c_312,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1963,plain,
    ( X0_52 != X1_52
    | X0_52 = k1_tsep_1(sK0,sK2,sK3)
    | k1_tsep_1(sK0,sK2,sK3) != X1_52 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_1964,plain,
    ( k1_tsep_1(sK0,sK2,sK3) != sK0
    | sK0 = k1_tsep_1(sK0,sK2,sK3)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1963])).

cnf(c_3899,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3225,c_32,c_33,c_34,c_38,c_39,c_40,c_41,c_351,c_284,c_1579,c_1675,c_1964])).

cnf(c_16,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_289,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52),X0_53,k10_tmap_1(X0_52,X3_52,X1_52,X2_52,k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X1_52,X0_53),k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X2_52,X0_53)))
    | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
    | ~ m1_pre_topc(X2_52,X0_52)
    | ~ m1_pre_topc(X1_52,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X0_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(X3_52)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_919,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52),X0_53,k10_tmap_1(X0_52,X3_52,X1_52,X2_52,k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X1_52,X0_53),k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X2_52,X0_53))) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
    | m1_pre_topc(X2_52,X0_52) != iProver_top
    | m1_pre_topc(X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_4501,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_919])).

cnf(c_4504,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4501,c_284])).

cnf(c_4509,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4504,c_32,c_33,c_34,c_38,c_39,c_40,c_41])).

cnf(c_4510,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4509])).

cnf(c_4522,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3899,c_4510])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5128,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4522,c_35,c_36,c_37,c_42,c_43,c_44])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X1,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_297,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | m1_subset_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_911,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52)))) = iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_3986,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_284,c_911])).

cnf(c_4658,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3986,c_32,c_33,c_34,c_38,c_39,c_40,c_41])).

cnf(c_4659,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4658])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_304,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X0_53,X1_53)
    | ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ v1_funct_2(X1_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | X0_53 = X1_53 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_904,plain,
    ( X0_53 = X1_53
    | r2_funct_2(X0_54,X1_54,X0_53,X1_53) != iProver_top
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(X1_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_304])).

cnf(c_1993,plain,
    ( sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_904])).

cnf(c_2242,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1993,c_42,c_43])).

cnf(c_2243,plain,
    ( sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2242])).

cnf(c_4681,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4659,c_2243])).

cnf(c_5241,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4681,c_35,c_36,c_37])).

cnf(c_5242,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
    | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5241])).

cnf(c_5258,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5128,c_5242])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_292,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | m1_subset_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_916,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) = iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_3902,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3899,c_916])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_291,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X3_52,X2_52)
    | ~ m1_pre_topc(X0_52,X2_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X2_52)
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X2_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_917,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52)) = iProver_top
    | m1_pre_topc(X0_52,X2_52) != iProver_top
    | m1_pre_topc(X3_52,X2_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_pre_topc(X2_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X2_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X2_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_3903,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3899,c_917])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_290,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
    | ~ m1_pre_topc(X2_52,X3_52)
    | ~ m1_pre_topc(X0_52,X3_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
    | ~ v2_pre_topc(X3_52)
    | ~ v2_pre_topc(X1_52)
    | v2_struct_0(X3_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X3_52)
    | ~ l1_pre_topc(X1_52)
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_918,plain,
    ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
    | m1_pre_topc(X2_52,X3_52) != iProver_top
    | m1_pre_topc(X0_52,X3_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
    | v2_pre_topc(X3_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X3_52) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X3_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_2580,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_918])).

cnf(c_3158,plain,
    ( v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2580,c_35,c_36,c_37,c_42,c_43])).

cnf(c_3159,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3158])).

cnf(c_3904,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3899,c_3159])).

cnf(c_1511,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(sK0,X1_52)
    | m1_subset_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_11687,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_52)
    | ~ m1_pre_topc(sK0,X0_52)
    | m1_subset_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_11692,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_pre_topc(sK0,X0_52) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11687])).

cnf(c_11694,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11692])).

cnf(c_1496,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(sK0,X1_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_290])).

cnf(c_13289,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_52)
    | ~ m1_pre_topc(sK0,X0_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK1)
    | v1_funct_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_13290,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_pre_topc(sK0,X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13289])).

cnf(c_13292,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_13290])).

cnf(c_1506,plain,
    ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,X1_52,sK4),u1_struct_0(X1_52),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X1_52,X0_52)
    | ~ m1_pre_topc(sK0,X0_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_14527,plain,
    ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_52)
    | ~ m1_pre_topc(sK0,X0_52)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1506])).

cnf(c_14530,plain,
    ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_pre_topc(sK0,X0_52) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14527])).

cnf(c_14532,plain,
    ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_14530])).

cnf(c_50740,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5258,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_351,c_284,c_1579,c_1675,c_1964,c_3902,c_3903,c_3904,c_11694,c_13292,c_14532])).

cnf(c_283,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_924,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_3184,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_3172])).

cnf(c_2397,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_924,c_2390])).

cnf(c_3238,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3184,c_2397])).

cnf(c_19509,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3238,c_32,c_33,c_34,c_38,c_39,c_40,c_41,c_351,c_284,c_1579,c_1675,c_1964])).

cnf(c_50744,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_50740,c_19509])).

cnf(c_17,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_321,plain,
    ( u1_struct_0(X0_52) = u1_struct_0(X1_52)
    | X0_52 != X1_52 ),
    theory(equality)).

cnf(c_339,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_308,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_352,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_303,plain,
    ( ~ l1_pre_topc(X0_52)
    | l1_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_279,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1574,plain,
    ( l1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_303,c_279])).

cnf(c_4,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_301,plain,
    ( r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X0_53)
    | ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ v1_funct_2(X0_53,X2_54,X3_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54)))
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X3_54)
    | ~ v1_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1491,plain,
    ( r1_funct_2(X0_54,X1_54,u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | ~ v1_funct_2(sK4,X0_54,X1_54)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(X1_54)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_1617,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_309,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_1923,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_302,plain,
    ( v2_struct_0(X0_52)
    | ~ v1_xboole_0(u1_struct_0(X0_52))
    | ~ l1_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3372,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_1614,plain,
    ( u1_struct_0(X0_52) = u1_struct_0(sK0)
    | X0_52 != sK0 ),
    inference(instantiation,[status(thm)],[c_321])).

cnf(c_5847,plain,
    ( u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)) = u1_struct_0(sK0)
    | k1_tsep_1(X0_52,X1_52,X2_52) != sK0 ),
    inference(instantiation,[status(thm)],[c_1614])).

cnf(c_7095,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) = u1_struct_0(sK0)
    | k1_tsep_1(sK0,sK2,sK3) != sK0 ),
    inference(instantiation,[status(thm)],[c_5847])).

cnf(c_324,plain,
    ( ~ r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X1_53)
    | r1_funct_2(X4_54,X5_54,X6_54,X7_54,X2_53,X3_53)
    | X4_54 != X0_54
    | X5_54 != X1_54
    | X6_54 != X2_54
    | X7_54 != X3_54
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_1704,plain,
    ( r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | X1_54 != u1_struct_0(sK1)
    | X3_54 != u1_struct_0(sK1)
    | X0_54 != u1_struct_0(sK0)
    | X2_54 != u1_struct_0(sK0)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_2366,plain,
    ( r1_funct_2(X0_54,X1_54,X2_54,u1_struct_0(sK1),X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | X1_54 != u1_struct_0(sK1)
    | X0_54 != u1_struct_0(sK0)
    | X2_54 != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_4564,plain,
    ( r1_funct_2(X0_54,u1_struct_0(sK1),X1_54,u1_struct_0(sK1),X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | X0_54 != u1_struct_0(sK0)
    | X1_54 != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_8789,plain,
    ( r1_funct_2(X0_54,u1_struct_0(sK1),u1_struct_0(X0_52),u1_struct_0(sK1),X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | X0_54 != u1_struct_0(sK0)
    | u1_struct_0(X0_52) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_4564])).

cnf(c_11349,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X0_52),u1_struct_0(sK1),X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | u1_struct_0(X0_52) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_8789])).

cnf(c_13611,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_11349])).

cnf(c_50749,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_50744,c_28,c_20,c_19,c_18,c_17,c_339,c_351,c_352,c_284,c_1574,c_1617,c_1923,c_3372,c_7095,c_13611])).

cnf(c_50753,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5112,c_50749])).

cnf(c_50754,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_50753])).

cnf(c_19517,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19509,c_3159])).

cnf(c_19728,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19517])).

cnf(c_19515,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_19509,c_917])).

cnf(c_19727,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19515])).

cnf(c_19514,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_19509,c_916])).

cnf(c_19726,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19514])).

cnf(c_3967,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3904])).

cnf(c_3966,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3903])).

cnf(c_3965,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3902])).

cnf(c_1674,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | m1_pre_topc(sK0,sK0)
    | sK0 != k1_tsep_1(sK0,sK2,sK3)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1672])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_125968,c_50754,c_19728,c_19727,c_19726,c_3967,c_3966,c_3965,c_1964,c_1674,c_1578,c_284,c_351,c_18,c_19,c_20,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:45:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.48/7.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.48/7.02  
% 51.48/7.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.48/7.02  
% 51.48/7.02  ------  iProver source info
% 51.48/7.02  
% 51.48/7.02  git: date: 2020-06-30 10:37:57 +0100
% 51.48/7.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.48/7.02  git: non_committed_changes: false
% 51.48/7.02  git: last_make_outside_of_git: false
% 51.48/7.02  
% 51.48/7.02  ------ 
% 51.48/7.02  ------ Parsing...
% 51.48/7.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.48/7.02  
% 51.48/7.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 51.48/7.02  
% 51.48/7.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.48/7.02  
% 51.48/7.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.48/7.02  ------ Proving...
% 51.48/7.02  ------ Problem Properties 
% 51.48/7.02  
% 51.48/7.02  
% 51.48/7.02  clauses                                 32
% 51.48/7.02  conjectures                             15
% 51.48/7.02  EPR                                     12
% 51.48/7.02  Horn                                    19
% 51.48/7.02  unary                                   15
% 51.48/7.02  binary                                  1
% 51.48/7.02  lits                                    189
% 51.48/7.02  lits eq                                 5
% 51.48/7.02  fd_pure                                 0
% 51.48/7.02  fd_pseudo                               0
% 51.48/7.02  fd_cond                                 0
% 51.48/7.02  fd_pseudo_cond                          2
% 51.48/7.02  AC symbols                              0
% 51.48/7.02  
% 51.48/7.02  ------ Input Options Time Limit: Unbounded
% 51.48/7.02  
% 51.48/7.02  
% 51.48/7.02  ------ 
% 51.48/7.02  Current options:
% 51.48/7.02  ------ 
% 51.48/7.02  
% 51.48/7.02  
% 51.48/7.02  
% 51.48/7.02  
% 51.48/7.02  ------ Proving...
% 51.48/7.02  
% 51.48/7.02  
% 51.48/7.02  % SZS status Theorem for theBenchmark.p
% 51.48/7.02  
% 51.48/7.02  % SZS output start CNFRefutation for theBenchmark.p
% 51.48/7.02  
% 51.48/7.02  fof(f7,axiom,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f25,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.48/7.02    inference(ennf_transformation,[],[f7])).
% 51.48/7.02  
% 51.48/7.02  fof(f26,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.48/7.02    inference(flattening,[],[f25])).
% 51.48/7.02  
% 51.48/7.02  fof(f51,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f26])).
% 51.48/7.02  
% 51.48/7.02  fof(f11,conjecture,(
% 51.48/7.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f12,negated_conjecture,(
% 51.48/7.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 51.48/7.02    inference(negated_conjecture,[],[f11])).
% 51.48/7.02  
% 51.48/7.02  fof(f33,plain,(
% 51.48/7.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 51.48/7.02    inference(ennf_transformation,[],[f12])).
% 51.48/7.02  
% 51.48/7.02  fof(f34,plain,(
% 51.48/7.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.48/7.02    inference(flattening,[],[f33])).
% 51.48/7.02  
% 51.48/7.02  fof(f41,plain,(
% 51.48/7.02    ( ! [X2,X0,X3,X1] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),sK4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,sK4,X2),k2_tmap_1(X0,X1,sK4,X3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 51.48/7.02    introduced(choice_axiom,[])).
% 51.48/7.02  
% 51.48/7.02  fof(f40,plain,(
% 51.48/7.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,sK3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,sK3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,sK3) = X0 & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 51.48/7.02    introduced(choice_axiom,[])).
% 51.48/7.02  
% 51.48/7.02  fof(f39,plain,(
% 51.48/7.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,sK2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,sK2,X3,k2_tmap_1(X0,X1,X4,sK2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,sK2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 51.48/7.02    introduced(choice_axiom,[])).
% 51.48/7.02  
% 51.48/7.02  fof(f38,plain,(
% 51.48/7.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(X0,sK1,X2,X3,k2_tmap_1(X0,sK1,X4,X2),k2_tmap_1(X0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 51.48/7.02    introduced(choice_axiom,[])).
% 51.48/7.02  
% 51.48/7.02  fof(f37,plain,(
% 51.48/7.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(sK0,X2,X3) = sK0 & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 51.48/7.02    introduced(choice_axiom,[])).
% 51.48/7.02  
% 51.48/7.02  fof(f42,plain,(
% 51.48/7.02    ((((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & k1_tsep_1(sK0,sK2,sK3) = sK0 & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 51.48/7.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f41,f40,f39,f38,f37])).
% 51.48/7.02  
% 51.48/7.02  fof(f70,plain,(
% 51.48/7.02    k1_tsep_1(sK0,sK2,sK3) = sK0),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f52,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f26])).
% 51.48/7.02  
% 51.48/7.02  fof(f60,plain,(
% 51.48/7.02    ~v2_struct_0(sK0)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f61,plain,(
% 51.48/7.02    v2_pre_topc(sK0)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f62,plain,(
% 51.48/7.02    l1_pre_topc(sK0)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f66,plain,(
% 51.48/7.02    ~v2_struct_0(sK2)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f67,plain,(
% 51.48/7.02    m1_pre_topc(sK2,sK0)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f68,plain,(
% 51.48/7.02    ~v2_struct_0(sK3)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f69,plain,(
% 51.48/7.02    m1_pre_topc(sK3,sK0)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f73,plain,(
% 51.48/7.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f6,axiom,(
% 51.48/7.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f23,plain,(
% 51.48/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.48/7.02    inference(ennf_transformation,[],[f6])).
% 51.48/7.02  
% 51.48/7.02  fof(f24,plain,(
% 51.48/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.48/7.02    inference(flattening,[],[f23])).
% 51.48/7.02  
% 51.48/7.02  fof(f50,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f24])).
% 51.48/7.02  
% 51.48/7.02  fof(f63,plain,(
% 51.48/7.02    ~v2_struct_0(sK1)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f64,plain,(
% 51.48/7.02    v2_pre_topc(sK1)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f65,plain,(
% 51.48/7.02    l1_pre_topc(sK1)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f71,plain,(
% 51.48/7.02    v1_funct_1(sK4)),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f72,plain,(
% 51.48/7.02    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f5,axiom,(
% 51.48/7.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f21,plain,(
% 51.48/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.48/7.02    inference(ennf_transformation,[],[f5])).
% 51.48/7.02  
% 51.48/7.02  fof(f22,plain,(
% 51.48/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.48/7.02    inference(flattening,[],[f21])).
% 51.48/7.02  
% 51.48/7.02  fof(f49,plain,(
% 51.48/7.02    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f22])).
% 51.48/7.02  
% 51.48/7.02  fof(f8,axiom,(
% 51.48/7.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f13,plain,(
% 51.48/7.02    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 51.48/7.02    inference(pure_predicate_removal,[],[f8])).
% 51.48/7.02  
% 51.48/7.02  fof(f27,plain,(
% 51.48/7.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 51.48/7.02    inference(ennf_transformation,[],[f13])).
% 51.48/7.02  
% 51.48/7.02  fof(f28,plain,(
% 51.48/7.02    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 51.48/7.02    inference(flattening,[],[f27])).
% 51.48/7.02  
% 51.48/7.02  fof(f55,plain,(
% 51.48/7.02    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f28])).
% 51.48/7.02  
% 51.48/7.02  fof(f10,axiom,(
% 51.48/7.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f31,plain,(
% 51.48/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.48/7.02    inference(ennf_transformation,[],[f10])).
% 51.48/7.02  
% 51.48/7.02  fof(f32,plain,(
% 51.48/7.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.48/7.02    inference(flattening,[],[f31])).
% 51.48/7.02  
% 51.48/7.02  fof(f59,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f32])).
% 51.48/7.02  
% 51.48/7.02  fof(f53,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f26])).
% 51.48/7.02  
% 51.48/7.02  fof(f1,axiom,(
% 51.48/7.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f14,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 51.48/7.02    inference(ennf_transformation,[],[f1])).
% 51.48/7.02  
% 51.48/7.02  fof(f15,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.48/7.02    inference(flattening,[],[f14])).
% 51.48/7.02  
% 51.48/7.02  fof(f35,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.48/7.02    inference(nnf_transformation,[],[f15])).
% 51.48/7.02  
% 51.48/7.02  fof(f43,plain,(
% 51.48/7.02    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f35])).
% 51.48/7.02  
% 51.48/7.02  fof(f9,axiom,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f29,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.48/7.02    inference(ennf_transformation,[],[f9])).
% 51.48/7.02  
% 51.48/7.02  fof(f30,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.48/7.02    inference(flattening,[],[f29])).
% 51.48/7.02  
% 51.48/7.02  fof(f58,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f30])).
% 51.48/7.02  
% 51.48/7.02  fof(f57,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f30])).
% 51.48/7.02  
% 51.48/7.02  fof(f56,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f30])).
% 51.48/7.02  
% 51.48/7.02  fof(f74,plain,(
% 51.48/7.02    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 51.48/7.02    inference(cnf_transformation,[],[f42])).
% 51.48/7.02  
% 51.48/7.02  fof(f2,axiom,(
% 51.48/7.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f16,plain,(
% 51.48/7.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 51.48/7.02    inference(ennf_transformation,[],[f2])).
% 51.48/7.02  
% 51.48/7.02  fof(f45,plain,(
% 51.48/7.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f16])).
% 51.48/7.02  
% 51.48/7.02  fof(f4,axiom,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f19,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 51.48/7.02    inference(ennf_transformation,[],[f4])).
% 51.48/7.02  
% 51.48/7.02  fof(f20,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 51.48/7.02    inference(flattening,[],[f19])).
% 51.48/7.02  
% 51.48/7.02  fof(f36,plain,(
% 51.48/7.02    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 51.48/7.02    inference(nnf_transformation,[],[f20])).
% 51.48/7.02  
% 51.48/7.02  fof(f48,plain,(
% 51.48/7.02    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f36])).
% 51.48/7.02  
% 51.48/7.02  fof(f76,plain,(
% 51.48/7.02    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 51.48/7.02    inference(equality_resolution,[],[f48])).
% 51.48/7.02  
% 51.48/7.02  fof(f3,axiom,(
% 51.48/7.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 51.48/7.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.48/7.02  
% 51.48/7.02  fof(f17,plain,(
% 51.48/7.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 51.48/7.02    inference(ennf_transformation,[],[f3])).
% 51.48/7.02  
% 51.48/7.02  fof(f18,plain,(
% 51.48/7.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 51.48/7.02    inference(flattening,[],[f17])).
% 51.48/7.02  
% 51.48/7.02  fof(f46,plain,(
% 51.48/7.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 51.48/7.02    inference(cnf_transformation,[],[f18])).
% 51.48/7.02  
% 51.48/7.02  cnf(c_10,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.48/7.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 51.48/7.02      | ~ m1_pre_topc(X4,X5)
% 51.48/7.02      | ~ m1_pre_topc(X1,X5)
% 51.48/7.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.48/7.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 51.48/7.02      | ~ v2_pre_topc(X2)
% 51.48/7.02      | ~ v2_pre_topc(X5)
% 51.48/7.02      | v2_struct_0(X5)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | v2_struct_0(X4)
% 51.48/7.02      | v2_struct_0(X1)
% 51.48/7.02      | ~ l1_pre_topc(X5)
% 51.48/7.02      | ~ l1_pre_topc(X2)
% 51.48/7.02      | ~ v1_funct_1(X3)
% 51.48/7.02      | ~ v1_funct_1(X0)
% 51.48/7.02      | v1_funct_1(k10_tmap_1(X5,X2,X1,X4,X0,X3)) ),
% 51.48/7.02      inference(cnf_transformation,[],[f51]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_295,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X3_52)
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X3_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ v2_pre_topc(X3_52)
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(X3_52)
% 51.48/7.02      | v2_struct_0(X2_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X3_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53)
% 51.48/7.02      | ~ v1_funct_1(X1_53)
% 51.48/7.02      | v1_funct_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53)) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_10]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_107494,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X2_52)
% 51.48/7.02      | ~ m1_pre_topc(X1_52,X2_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
% 51.48/7.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(X2_52)
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(X2_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | ~ l1_pre_topc(X2_52)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ v1_funct_1(X0_53)
% 51.48/7.02      | ~ v1_funct_1(X1_53)
% 51.48/7.02      | v1_funct_1(k10_tmap_1(X2_52,sK1,X0_52,X1_52,X0_53,X1_53)) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_295]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_125968,plain,
% 51.48/7.02      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(sK3,sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK2,sK0)
% 51.48/7.02      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 51.48/7.02      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | ~ v2_pre_topc(sK0)
% 51.48/7.02      | v2_struct_0(sK3)
% 51.48/7.02      | v2_struct_0(sK2)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ l1_pre_topc(sK0)
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 51.48/7.02      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 51.48/7.02      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_107494]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_21,negated_conjecture,
% 51.48/7.02      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 51.48/7.02      inference(cnf_transformation,[],[f70]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_284,negated_conjecture,
% 51.48/7.02      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_21]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_9,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.48/7.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 51.48/7.02      | v1_funct_2(k10_tmap_1(X5,X2,X1,X4,X0,X3),u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))
% 51.48/7.02      | ~ m1_pre_topc(X4,X5)
% 51.48/7.02      | ~ m1_pre_topc(X1,X5)
% 51.48/7.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.48/7.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 51.48/7.02      | ~ v2_pre_topc(X2)
% 51.48/7.02      | ~ v2_pre_topc(X5)
% 51.48/7.02      | v2_struct_0(X5)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | v2_struct_0(X4)
% 51.48/7.02      | v2_struct_0(X1)
% 51.48/7.02      | ~ l1_pre_topc(X5)
% 51.48/7.02      | ~ l1_pre_topc(X2)
% 51.48/7.02      | ~ v1_funct_1(X3)
% 51.48/7.02      | ~ v1_funct_1(X0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f52]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_296,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 51.48/7.02      | v1_funct_2(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52))
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X3_52)
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X3_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ v2_pre_topc(X3_52)
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(X3_52)
% 51.48/7.02      | v2_struct_0(X2_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X3_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53)
% 51.48/7.02      | ~ v1_funct_1(X1_53) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_9]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_912,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52)) = iProver_top
% 51.48/7.02      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X3_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X2_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4986,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK3) = iProver_top
% 51.48/7.02      | v2_struct_0(sK2) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_284,c_912]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_31,negated_conjecture,
% 51.48/7.02      ( ~ v2_struct_0(sK0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f60]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_32,plain,
% 51.48/7.02      ( v2_struct_0(sK0) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_30,negated_conjecture,
% 51.48/7.02      ( v2_pre_topc(sK0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f61]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_33,plain,
% 51.48/7.02      ( v2_pre_topc(sK0) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_29,negated_conjecture,
% 51.48/7.02      ( l1_pre_topc(sK0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f62]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_34,plain,
% 51.48/7.02      ( l1_pre_topc(sK0) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_25,negated_conjecture,
% 51.48/7.02      ( ~ v2_struct_0(sK2) ),
% 51.48/7.02      inference(cnf_transformation,[],[f66]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_38,plain,
% 51.48/7.02      ( v2_struct_0(sK2) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_24,negated_conjecture,
% 51.48/7.02      ( m1_pre_topc(sK2,sK0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f67]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_39,plain,
% 51.48/7.02      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_23,negated_conjecture,
% 51.48/7.02      ( ~ v2_struct_0(sK3) ),
% 51.48/7.02      inference(cnf_transformation,[],[f68]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_40,plain,
% 51.48/7.02      ( v2_struct_0(sK3) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_22,negated_conjecture,
% 51.48/7.02      ( m1_pre_topc(sK3,sK0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f69]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_41,plain,
% 51.48/7.02      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_5111,plain,
% 51.48/7.02      ( l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_4986,c_32,c_33,c_34,c_38,c_39,c_40,c_41]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_5112,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top ),
% 51.48/7.02      inference(renaming,[status(thm)],[c_5111]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_281,negated_conjecture,
% 51.48/7.02      ( m1_pre_topc(sK2,sK0) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_24]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_926,plain,
% 51.48/7.02      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_18,negated_conjecture,
% 51.48/7.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 51.48/7.02      inference(cnf_transformation,[],[f73]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_287,negated_conjecture,
% 51.48/7.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_18]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_921,plain,
% 51.48/7.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_7,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.48/7.02      | ~ m1_pre_topc(X3,X4)
% 51.48/7.02      | ~ m1_pre_topc(X3,X1)
% 51.48/7.02      | ~ m1_pre_topc(X1,X4)
% 51.48/7.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.48/7.02      | ~ v2_pre_topc(X2)
% 51.48/7.02      | ~ v2_pre_topc(X4)
% 51.48/7.02      | v2_struct_0(X4)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | ~ l1_pre_topc(X4)
% 51.48/7.02      | ~ l1_pre_topc(X2)
% 51.48/7.02      | ~ v1_funct_1(X0)
% 51.48/7.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f50]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_298,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X0_52)
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X3_52)
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X3_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ v2_pre_topc(X3_52)
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | v2_struct_0(X3_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X3_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53)
% 51.48/7.02      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_7]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_910,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X3_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2563,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 51.48/7.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_921,c_910]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_28,negated_conjecture,
% 51.48/7.02      ( ~ v2_struct_0(sK1) ),
% 51.48/7.02      inference(cnf_transformation,[],[f63]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_35,plain,
% 51.48/7.02      ( v2_struct_0(sK1) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_27,negated_conjecture,
% 51.48/7.02      ( v2_pre_topc(sK1) ),
% 51.48/7.02      inference(cnf_transformation,[],[f64]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_36,plain,
% 51.48/7.02      ( v2_pre_topc(sK1) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_26,negated_conjecture,
% 51.48/7.02      ( l1_pre_topc(sK1) ),
% 51.48/7.02      inference(cnf_transformation,[],[f65]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_37,plain,
% 51.48/7.02      ( l1_pre_topc(sK1) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_20,negated_conjecture,
% 51.48/7.02      ( v1_funct_1(sK4) ),
% 51.48/7.02      inference(cnf_transformation,[],[f71]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_42,plain,
% 51.48/7.02      ( v1_funct_1(sK4) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_19,negated_conjecture,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 51.48/7.02      inference(cnf_transformation,[],[f72]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_43,plain,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3171,plain,
% 51.48/7.02      ( v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 51.48/7.02      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_2563,c_35,c_36,c_37,c_42,c_43,c_44,c_1530]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3172,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 51.48/7.02      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top ),
% 51.48/7.02      inference(renaming,[status(thm)],[c_3171]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3185,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_926,c_3172]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_6,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.48/7.02      | ~ m1_pre_topc(X3,X1)
% 51.48/7.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.48/7.02      | ~ v2_pre_topc(X2)
% 51.48/7.02      | ~ v2_pre_topc(X1)
% 51.48/7.02      | v2_struct_0(X1)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | ~ l1_pre_topc(X1)
% 51.48/7.02      | ~ l1_pre_topc(X2)
% 51.48/7.02      | ~ v1_funct_1(X0)
% 51.48/7.02      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 51.48/7.02      inference(cnf_transformation,[],[f49]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_299,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X0_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ v2_pre_topc(X0_52)
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X0_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53)
% 51.48/7.02      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_6]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_909,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52)
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2384,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
% 51.48/7.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,sK0) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_921,c_909]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2389,plain,
% 51.48/7.02      ( m1_pre_topc(X0_52,sK0) != iProver_top
% 51.48/7.02      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52) ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_2384,c_32,c_33,c_34,c_35,c_36,c_37,c_42,c_43]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2390,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
% 51.48/7.02      | m1_pre_topc(X0_52,sK0) != iProver_top ),
% 51.48/7.02      inference(renaming,[status(thm)],[c_2389]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2398,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_926,c_2390]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3225,plain,
% 51.48/7.02      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top ),
% 51.48/7.02      inference(light_normalisation,[status(thm)],[c_3185,c_2398]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_307,plain,( X0_52 = X0_52 ),theory(equality) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_351,plain,
% 51.48/7.02      ( sK0 = sK0 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_307]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_11,plain,
% 51.48/7.02      ( ~ m1_pre_topc(X0,X1)
% 51.48/7.02      | ~ m1_pre_topc(X2,X1)
% 51.48/7.02      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 51.48/7.02      | v2_struct_0(X1)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | v2_struct_0(X0)
% 51.48/7.02      | ~ l1_pre_topc(X1) ),
% 51.48/7.02      inference(cnf_transformation,[],[f55]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_294,plain,
% 51.48/7.02      ( ~ m1_pre_topc(X0_52,X1_52)
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X1_52)
% 51.48/7.02      | m1_pre_topc(k1_tsep_1(X1_52,X2_52,X0_52),X1_52)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(X2_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_11]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1467,plain,
% 51.48/7.02      ( ~ m1_pre_topc(X0_52,sK0)
% 51.48/7.02      | m1_pre_topc(k1_tsep_1(sK0,sK2,X0_52),sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK2,sK0)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(sK2)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK0) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_294]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1578,plain,
% 51.48/7.02      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK3,sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK2,sK0)
% 51.48/7.02      | v2_struct_0(sK3)
% 51.48/7.02      | v2_struct_0(sK2)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK0) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1467]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1579,plain,
% 51.48/7.02      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) = iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK3) = iProver_top
% 51.48/7.02      | v2_struct_0(sK2) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_1578]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_327,plain,
% 51.48/7.02      ( ~ m1_pre_topc(X0_52,X1_52)
% 51.48/7.02      | m1_pre_topc(X2_52,X3_52)
% 51.48/7.02      | X2_52 != X0_52
% 51.48/7.02      | X3_52 != X1_52 ),
% 51.48/7.02      theory(equality) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1672,plain,
% 51.48/7.02      ( m1_pre_topc(X0_52,X1_52)
% 51.48/7.02      | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
% 51.48/7.02      | X0_52 != k1_tsep_1(sK0,sK2,sK3)
% 51.48/7.02      | X1_52 != sK0 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_327]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1673,plain,
% 51.48/7.02      ( X0_52 != k1_tsep_1(sK0,sK2,sK3)
% 51.48/7.02      | X1_52 != sK0
% 51.48/7.02      | m1_pre_topc(X0_52,X1_52) = iProver_top
% 51.48/7.02      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_1672]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1675,plain,
% 51.48/7.02      ( sK0 != k1_tsep_1(sK0,sK2,sK3)
% 51.48/7.02      | sK0 != sK0
% 51.48/7.02      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) = iProver_top ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1673]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_312,plain,
% 51.48/7.02      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 51.48/7.02      theory(equality) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1963,plain,
% 51.48/7.02      ( X0_52 != X1_52
% 51.48/7.02      | X0_52 = k1_tsep_1(sK0,sK2,sK3)
% 51.48/7.02      | k1_tsep_1(sK0,sK2,sK3) != X1_52 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_312]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1964,plain,
% 51.48/7.02      ( k1_tsep_1(sK0,sK2,sK3) != sK0
% 51.48/7.02      | sK0 = k1_tsep_1(sK0,sK2,sK3)
% 51.48/7.02      | sK0 != sK0 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1963]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3899,plain,
% 51.48/7.02      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_3225,c_32,c_33,c_34,c_38,c_39,c_40,c_41,c_351,c_284,
% 51.48/7.02                 c_1579,c_1675,c_1964]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_16,plain,
% 51.48/7.02      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
% 51.48/7.02      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
% 51.48/7.02      | ~ m1_pre_topc(X2,X0)
% 51.48/7.02      | ~ m1_pre_topc(X1,X0)
% 51.48/7.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
% 51.48/7.02      | ~ v2_pre_topc(X3)
% 51.48/7.02      | ~ v2_pre_topc(X0)
% 51.48/7.02      | v2_struct_0(X0)
% 51.48/7.02      | v2_struct_0(X3)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | v2_struct_0(X1)
% 51.48/7.02      | ~ l1_pre_topc(X0)
% 51.48/7.02      | ~ l1_pre_topc(X3)
% 51.48/7.02      | ~ v1_funct_1(X4) ),
% 51.48/7.02      inference(cnf_transformation,[],[f59]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_289,plain,
% 51.48/7.02      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52),X0_53,k10_tmap_1(X0_52,X3_52,X1_52,X2_52,k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X1_52,X0_53),k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X2_52,X0_53)))
% 51.48/7.02      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X0_52)
% 51.48/7.02      | ~ m1_pre_topc(X1_52,X0_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
% 51.48/7.02      | ~ v2_pre_topc(X3_52)
% 51.48/7.02      | ~ v2_pre_topc(X0_52)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(X3_52)
% 51.48/7.02      | v2_struct_0(X2_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X0_52)
% 51.48/7.02      | ~ l1_pre_topc(X3_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_16]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_919,plain,
% 51.48/7.02      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52),X0_53,k10_tmap_1(X0_52,X3_52,X1_52,X2_52,k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X1_52,X0_53),k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X2_52,X0_53))) = iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X3_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X2_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4501,plain,
% 51.48/7.02      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK3) = iProver_top
% 51.48/7.02      | v2_struct_0(sK2) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_284,c_919]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4504,plain,
% 51.48/7.02      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK3) = iProver_top
% 51.48/7.02      | v2_struct_0(sK2) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(light_normalisation,[status(thm)],[c_4501,c_284]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4509,plain,
% 51.48/7.02      ( l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_4504,c_32,c_33,c_34,c_38,c_39,c_40,c_41]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4510,plain,
% 51.48/7.02      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(renaming,[status(thm)],[c_4509]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4522,plain,
% 51.48/7.02      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top
% 51.48/7.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_3899,c_4510]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_44,plain,
% 51.48/7.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_5128,plain,
% 51.48/7.02      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_4522,c_35,c_36,c_37,c_42,c_43,c_44]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_8,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.48/7.02      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 51.48/7.02      | ~ m1_pre_topc(X4,X5)
% 51.48/7.02      | ~ m1_pre_topc(X1,X5)
% 51.48/7.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.48/7.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 51.48/7.02      | m1_subset_1(k10_tmap_1(X5,X2,X1,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))))
% 51.48/7.02      | ~ v2_pre_topc(X2)
% 51.48/7.02      | ~ v2_pre_topc(X5)
% 51.48/7.02      | v2_struct_0(X5)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | v2_struct_0(X4)
% 51.48/7.02      | v2_struct_0(X1)
% 51.48/7.02      | ~ l1_pre_topc(X5)
% 51.48/7.02      | ~ l1_pre_topc(X2)
% 51.48/7.02      | ~ v1_funct_1(X3)
% 51.48/7.02      | ~ v1_funct_1(X0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f53]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_297,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X3_52)
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X3_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 51.48/7.02      | m1_subset_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ v2_pre_topc(X3_52)
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(X3_52)
% 51.48/7.02      | v2_struct_0(X2_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X3_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53)
% 51.48/7.02      | ~ v1_funct_1(X1_53) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_8]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_911,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52)))) = iProver_top
% 51.48/7.02      | v2_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X3_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X2_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3986,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK3) = iProver_top
% 51.48/7.02      | v2_struct_0(sK2) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_284,c_911]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4658,plain,
% 51.48/7.02      ( l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_3986,c_32,c_33,c_34,c_38,c_39,c_40,c_41]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4659,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top ),
% 51.48/7.02      inference(renaming,[status(thm)],[c_4658]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1,plain,
% 51.48/7.02      ( ~ r2_funct_2(X0,X1,X2,X3)
% 51.48/7.02      | ~ v1_funct_2(X3,X0,X1)
% 51.48/7.02      | ~ v1_funct_2(X2,X0,X1)
% 51.48/7.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.48/7.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.48/7.02      | ~ v1_funct_1(X3)
% 51.48/7.02      | ~ v1_funct_1(X2)
% 51.48/7.02      | X2 = X3 ),
% 51.48/7.02      inference(cnf_transformation,[],[f43]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_304,plain,
% 51.48/7.02      ( ~ r2_funct_2(X0_54,X1_54,X0_53,X1_53)
% 51.48/7.02      | ~ v1_funct_2(X0_53,X0_54,X1_54)
% 51.48/7.02      | ~ v1_funct_2(X1_53,X0_54,X1_54)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 51.48/7.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 51.48/7.02      | ~ v1_funct_1(X0_53)
% 51.48/7.02      | ~ v1_funct_1(X1_53)
% 51.48/7.02      | X0_53 = X1_53 ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_1]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_904,plain,
% 51.48/7.02      ( X0_53 = X1_53
% 51.48/7.02      | r2_funct_2(X0_54,X1_54,X0_53,X1_53) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,X0_54,X1_54) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_304]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1993,plain,
% 51.48/7.02      ( sK4 = X0_53
% 51.48/7.02      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_921,c_904]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2242,plain,
% 51.48/7.02      ( v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | sK4 = X0_53
% 51.48/7.02      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_1993,c_42,c_43]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2243,plain,
% 51.48/7.02      ( sK4 = X0_53
% 51.48/7.02      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(renaming,[status(thm)],[c_2242]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4681,plain,
% 51.48/7.02      ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
% 51.48/7.02      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_4659,c_2243]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_5241,plain,
% 51.48/7.02      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
% 51.48/7.02      | k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_4681,c_35,c_36,c_37]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_5242,plain,
% 51.48/7.02      ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
% 51.48/7.02      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
% 51.48/7.02      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(X1_53) != iProver_top
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
% 51.48/7.02      inference(renaming,[status(thm)],[c_5241]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_5258,plain,
% 51.48/7.02      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 51.48/7.02      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 51.48/7.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_5128,c_5242]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_13,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.48/7.02      | ~ m1_pre_topc(X3,X4)
% 51.48/7.02      | ~ m1_pre_topc(X1,X4)
% 51.48/7.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.48/7.02      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 51.48/7.02      | ~ v2_pre_topc(X2)
% 51.48/7.02      | ~ v2_pre_topc(X4)
% 51.48/7.02      | v2_struct_0(X4)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | ~ l1_pre_topc(X4)
% 51.48/7.02      | ~ l1_pre_topc(X2)
% 51.48/7.02      | ~ v1_funct_1(X0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f58]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_292,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X3_52)
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X3_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.48/7.02      | m1_subset_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ v2_pre_topc(X3_52)
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | v2_struct_0(X3_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X3_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_13]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_916,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | m1_subset_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) = iProver_top
% 51.48/7.02      | v2_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X3_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3902,plain,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_3899,c_916]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_14,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.48/7.02      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 51.48/7.02      | ~ m1_pre_topc(X4,X3)
% 51.48/7.02      | ~ m1_pre_topc(X1,X3)
% 51.48/7.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.48/7.02      | ~ v2_pre_topc(X2)
% 51.48/7.02      | ~ v2_pre_topc(X3)
% 51.48/7.02      | v2_struct_0(X3)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | ~ l1_pre_topc(X3)
% 51.48/7.02      | ~ l1_pre_topc(X2)
% 51.48/7.02      | ~ v1_funct_1(X0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f57]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_291,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.48/7.02      | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ m1_pre_topc(X3_52,X2_52)
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X2_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ v2_pre_topc(X2_52)
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | v2_struct_0(X2_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X2_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_14]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_917,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52)) = iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X3_52,X2_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X2_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X2_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X2_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3903,plain,
% 51.48/7.02      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 51.48/7.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_3899,c_917]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_15,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.48/7.02      | ~ m1_pre_topc(X3,X4)
% 51.48/7.02      | ~ m1_pre_topc(X1,X4)
% 51.48/7.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.48/7.02      | ~ v2_pre_topc(X2)
% 51.48/7.02      | ~ v2_pre_topc(X4)
% 51.48/7.02      | v2_struct_0(X4)
% 51.48/7.02      | v2_struct_0(X2)
% 51.48/7.02      | ~ l1_pre_topc(X4)
% 51.48/7.02      | ~ l1_pre_topc(X2)
% 51.48/7.02      | ~ v1_funct_1(X0)
% 51.48/7.02      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 51.48/7.02      inference(cnf_transformation,[],[f56]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_290,plain,
% 51.48/7.02      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.48/7.02      | ~ m1_pre_topc(X2_52,X3_52)
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X3_52)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.48/7.02      | ~ v2_pre_topc(X3_52)
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | v2_struct_0(X3_52)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(X3_52)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ v1_funct_1(X0_53)
% 51.48/7.02      | v1_funct_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_15]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_918,plain,
% 51.48/7.02      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.48/7.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X3_52) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X3_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v1_funct_1(X0_53) != iProver_top
% 51.48/7.02      | v1_funct_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2580,plain,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_921,c_918]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3158,plain,
% 51.48/7.02      ( v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_2580,c_35,c_36,c_37,c_42,c_43]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3159,plain,
% 51.48/7.02      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v2_struct_0(X1_52) = iProver_top
% 51.48/7.02      | l1_pre_topc(X1_52) != iProver_top
% 51.48/7.02      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top ),
% 51.48/7.02      inference(renaming,[status(thm)],[c_3158]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3904,plain,
% 51.48/7.02      ( m1_pre_topc(sK2,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_3899,c_3159]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1511,plain,
% 51.48/7.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X1_52)
% 51.48/7.02      | ~ m1_pre_topc(sK0,X1_52)
% 51.48/7.02      | m1_subset_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_292]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_11687,plain,
% 51.48/7.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(sK3,X0_52)
% 51.48/7.02      | ~ m1_pre_topc(sK0,X0_52)
% 51.48/7.02      | m1_subset_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(X0_52)
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | ~ l1_pre_topc(X0_52)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1511]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_11692,plain,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,X0_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X0_52) != iProver_top
% 51.48/7.02      | m1_subset_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_11687]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_11694,plain,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_11692]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1496,plain,
% 51.48/7.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(X0_52,X1_52)
% 51.48/7.02      | ~ m1_pre_topc(sK0,X1_52)
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(X1_52)
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | v2_struct_0(X1_52)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | ~ l1_pre_topc(X1_52)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4))
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_290]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_13289,plain,
% 51.48/7.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(sK3,X0_52)
% 51.48/7.02      | ~ m1_pre_topc(sK0,X0_52)
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(X0_52)
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | ~ l1_pre_topc(X0_52)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | v1_funct_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4))
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1496]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_13290,plain,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,X0_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X0_52) != iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v1_funct_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4)) = iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_13289]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_13292,plain,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_13290]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1506,plain,
% 51.48/7.02      ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,X1_52,sK4),u1_struct_0(X1_52),u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(X1_52,X0_52)
% 51.48/7.02      | ~ m1_pre_topc(sK0,X0_52)
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(X0_52)
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | ~ l1_pre_topc(X0_52)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_291]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_14527,plain,
% 51.48/7.02      ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(sK3,X0_52)
% 51.48/7.02      | ~ m1_pre_topc(sK0,X0_52)
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(X0_52)
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | v2_struct_0(X0_52)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | ~ l1_pre_topc(X0_52)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1506]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_14530,plain,
% 51.48/7.02      ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 51.48/7.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,X0_52) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,X0_52) != iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_struct_0(X0_52) = iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | l1_pre_topc(X0_52) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_14527]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_14532,plain,
% 51.48/7.02      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 51.48/7.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_14530]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_50740,plain,
% 51.48/7.02      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_5258,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,
% 51.48/7.02                 c_41,c_42,c_43,c_44,c_351,c_284,c_1579,c_1675,c_1964,
% 51.48/7.02                 c_3902,c_3903,c_3904,c_11694,c_13292,c_14532]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_283,negated_conjecture,
% 51.48/7.02      ( m1_pre_topc(sK3,sK0) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_22]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_924,plain,
% 51.48/7.02      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 51.48/7.02      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3184,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_924,c_3172]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2397,plain,
% 51.48/7.02      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_924,c_2390]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3238,plain,
% 51.48/7.02      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top ),
% 51.48/7.02      inference(light_normalisation,[status(thm)],[c_3184,c_2397]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_19509,plain,
% 51.48/7.02      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_3238,c_32,c_33,c_34,c_38,c_39,c_40,c_41,c_351,c_284,
% 51.48/7.02                 c_1579,c_1675,c_1964]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_50744,plain,
% 51.48/7.02      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 51.48/7.02      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
% 51.48/7.02      inference(light_normalisation,[status(thm)],[c_50740,c_19509]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_17,negated_conjecture,
% 51.48/7.02      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
% 51.48/7.02      inference(cnf_transformation,[],[f74]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_321,plain,
% 51.48/7.02      ( u1_struct_0(X0_52) = u1_struct_0(X1_52) | X0_52 != X1_52 ),
% 51.48/7.02      theory(equality) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_339,plain,
% 51.48/7.02      ( u1_struct_0(sK0) = u1_struct_0(sK0) | sK0 != sK0 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_321]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_308,plain,( X0_53 = X0_53 ),theory(equality) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_352,plain,
% 51.48/7.02      ( sK4 = sK4 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_308]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2,plain,
% 51.48/7.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f45]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_303,plain,
% 51.48/7.02      ( ~ l1_pre_topc(X0_52) | l1_struct_0(X0_52) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_2]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_279,negated_conjecture,
% 51.48/7.02      ( l1_pre_topc(sK1) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_26]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1574,plain,
% 51.48/7.02      ( l1_struct_0(sK1) ),
% 51.48/7.02      inference(resolution,[status(thm)],[c_303,c_279]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4,plain,
% 51.48/7.02      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 51.48/7.02      | ~ v1_funct_2(X4,X2,X3)
% 51.48/7.02      | ~ v1_funct_2(X4,X0,X1)
% 51.48/7.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 51.48/7.02      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.48/7.02      | v1_xboole_0(X1)
% 51.48/7.02      | v1_xboole_0(X3)
% 51.48/7.02      | ~ v1_funct_1(X4) ),
% 51.48/7.02      inference(cnf_transformation,[],[f76]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_301,plain,
% 51.48/7.02      ( r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X0_53)
% 51.48/7.02      | ~ v1_funct_2(X0_53,X0_54,X1_54)
% 51.48/7.02      | ~ v1_funct_2(X0_53,X2_54,X3_54)
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 51.48/7.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54)))
% 51.48/7.02      | v1_xboole_0(X1_54)
% 51.48/7.02      | v1_xboole_0(X3_54)
% 51.48/7.02      | ~ v1_funct_1(X0_53) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_4]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1491,plain,
% 51.48/7.02      ( r1_funct_2(X0_54,X1_54,u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.48/7.02      | ~ v1_funct_2(sK4,X0_54,X1_54)
% 51.48/7.02      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | v1_xboole_0(X1_54)
% 51.48/7.02      | v1_xboole_0(u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_301]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1617,plain,
% 51.48/7.02      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.48/7.02      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | v1_xboole_0(u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1491]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_309,plain,( X0_54 = X0_54 ),theory(equality) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1923,plain,
% 51.48/7.02      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_309]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3,plain,
% 51.48/7.02      ( v2_struct_0(X0)
% 51.48/7.02      | ~ v1_xboole_0(u1_struct_0(X0))
% 51.48/7.02      | ~ l1_struct_0(X0) ),
% 51.48/7.02      inference(cnf_transformation,[],[f46]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_302,plain,
% 51.48/7.02      ( v2_struct_0(X0_52)
% 51.48/7.02      | ~ v1_xboole_0(u1_struct_0(X0_52))
% 51.48/7.02      | ~ l1_struct_0(X0_52) ),
% 51.48/7.02      inference(subtyping,[status(esa)],[c_3]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3372,plain,
% 51.48/7.02      ( v2_struct_0(sK1)
% 51.48/7.02      | ~ v1_xboole_0(u1_struct_0(sK1))
% 51.48/7.02      | ~ l1_struct_0(sK1) ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_302]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1614,plain,
% 51.48/7.02      ( u1_struct_0(X0_52) = u1_struct_0(sK0) | X0_52 != sK0 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_321]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_5847,plain,
% 51.48/7.02      ( u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)) = u1_struct_0(sK0)
% 51.48/7.02      | k1_tsep_1(X0_52,X1_52,X2_52) != sK0 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1614]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_7095,plain,
% 51.48/7.02      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) = u1_struct_0(sK0)
% 51.48/7.02      | k1_tsep_1(sK0,sK2,sK3) != sK0 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_5847]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_324,plain,
% 51.48/7.02      ( ~ r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X1_53)
% 51.48/7.02      | r1_funct_2(X4_54,X5_54,X6_54,X7_54,X2_53,X3_53)
% 51.48/7.02      | X4_54 != X0_54
% 51.48/7.02      | X5_54 != X1_54
% 51.48/7.02      | X6_54 != X2_54
% 51.48/7.02      | X7_54 != X3_54
% 51.48/7.02      | X2_53 != X0_53
% 51.48/7.02      | X3_53 != X1_53 ),
% 51.48/7.02      theory(equality) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1704,plain,
% 51.48/7.02      ( r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X1_53)
% 51.48/7.02      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.48/7.02      | X1_54 != u1_struct_0(sK1)
% 51.48/7.02      | X3_54 != u1_struct_0(sK1)
% 51.48/7.02      | X0_54 != u1_struct_0(sK0)
% 51.48/7.02      | X2_54 != u1_struct_0(sK0)
% 51.48/7.02      | X0_53 != sK4
% 51.48/7.02      | X1_53 != sK4 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_324]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_2366,plain,
% 51.48/7.02      ( r1_funct_2(X0_54,X1_54,X2_54,u1_struct_0(sK1),X0_53,X1_53)
% 51.48/7.02      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.48/7.02      | X1_54 != u1_struct_0(sK1)
% 51.48/7.02      | X0_54 != u1_struct_0(sK0)
% 51.48/7.02      | X2_54 != u1_struct_0(sK0)
% 51.48/7.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.48/7.02      | X0_53 != sK4
% 51.48/7.02      | X1_53 != sK4 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1704]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_4564,plain,
% 51.48/7.02      ( r1_funct_2(X0_54,u1_struct_0(sK1),X1_54,u1_struct_0(sK1),X0_53,X1_53)
% 51.48/7.02      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.48/7.02      | X0_54 != u1_struct_0(sK0)
% 51.48/7.02      | X1_54 != u1_struct_0(sK0)
% 51.48/7.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.48/7.02      | X0_53 != sK4
% 51.48/7.02      | X1_53 != sK4 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_2366]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_8789,plain,
% 51.48/7.02      ( r1_funct_2(X0_54,u1_struct_0(sK1),u1_struct_0(X0_52),u1_struct_0(sK1),X0_53,X1_53)
% 51.48/7.02      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.48/7.02      | X0_54 != u1_struct_0(sK0)
% 51.48/7.02      | u1_struct_0(X0_52) != u1_struct_0(sK0)
% 51.48/7.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.48/7.02      | X0_53 != sK4
% 51.48/7.02      | X1_53 != sK4 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_4564]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_11349,plain,
% 51.48/7.02      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X0_52),u1_struct_0(sK1),X0_53,X1_53)
% 51.48/7.02      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.48/7.02      | u1_struct_0(X0_52) != u1_struct_0(sK0)
% 51.48/7.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.48/7.02      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 51.48/7.02      | X0_53 != sK4
% 51.48/7.02      | X1_53 != sK4 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_8789]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_13611,plain,
% 51.48/7.02      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 51.48/7.02      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.48/7.02      | u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) != u1_struct_0(sK0)
% 51.48/7.02      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.48/7.02      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 51.48/7.02      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 51.48/7.02      | sK4 != sK4 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_11349]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_50749,plain,
% 51.48/7.02      ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
% 51.48/7.02      inference(global_propositional_subsumption,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_50744,c_28,c_20,c_19,c_18,c_17,c_339,c_351,c_352,
% 51.48/7.02                 c_284,c_1574,c_1617,c_1923,c_3372,c_7095,c_13611]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_50753,plain,
% 51.48/7.02      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 51.48/7.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 51.48/7.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_5112,c_50749]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_50754,plain,
% 51.48/7.02      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 51.48/7.02      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 51.48/7.02      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 51.48/7.02      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 51.48/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_50753]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_19517,plain,
% 51.48/7.02      ( m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_19509,c_3159]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_19728,plain,
% 51.48/7.02      ( ~ m1_pre_topc(sK3,sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK0,sK0)
% 51.48/7.02      | ~ v2_pre_topc(sK0)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK0)
% 51.48/7.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 51.48/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_19517]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_19515,plain,
% 51.48/7.02      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 51.48/7.02      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_19509,c_917]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_19727,plain,
% 51.48/7.02      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(sK3,sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK0,sK0)
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | ~ v2_pre_topc(sK0)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ l1_pre_topc(sK0)
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_19515]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_19514,plain,
% 51.48/7.02      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.48/7.02      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.48/7.02      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 51.48/7.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK1) != iProver_top
% 51.48/7.02      | v2_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v2_struct_0(sK1) = iProver_top
% 51.48/7.02      | v2_struct_0(sK0) = iProver_top
% 51.48/7.02      | l1_pre_topc(sK1) != iProver_top
% 51.48/7.02      | l1_pre_topc(sK0) != iProver_top
% 51.48/7.02      | v1_funct_1(sK4) != iProver_top ),
% 51.48/7.02      inference(superposition,[status(thm)],[c_19509,c_916]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_19726,plain,
% 51.48/7.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(sK3,sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK0,sK0)
% 51.48/7.02      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | ~ v2_pre_topc(sK0)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ l1_pre_topc(sK0)
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_19514]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3967,plain,
% 51.48/7.02      ( ~ m1_pre_topc(sK2,sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK0,sK0)
% 51.48/7.02      | ~ v2_pre_topc(sK0)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK0)
% 51.48/7.02      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 51.48/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_3904]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3966,plain,
% 51.48/7.02      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 51.48/7.02      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(sK2,sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK0,sK0)
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | ~ v2_pre_topc(sK0)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ l1_pre_topc(sK0)
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_3903]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_3965,plain,
% 51.48/7.02      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.48/7.02      | ~ m1_pre_topc(sK2,sK0)
% 51.48/7.02      | ~ m1_pre_topc(sK0,sK0)
% 51.48/7.02      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 51.48/7.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.48/7.02      | ~ v2_pre_topc(sK1)
% 51.48/7.02      | ~ v2_pre_topc(sK0)
% 51.48/7.02      | v2_struct_0(sK1)
% 51.48/7.02      | v2_struct_0(sK0)
% 51.48/7.02      | ~ l1_pre_topc(sK1)
% 51.48/7.02      | ~ l1_pre_topc(sK0)
% 51.48/7.02      | ~ v1_funct_1(sK4) ),
% 51.48/7.02      inference(predicate_to_equality_rev,[status(thm)],[c_3902]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(c_1674,plain,
% 51.48/7.02      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
% 51.48/7.02      | m1_pre_topc(sK0,sK0)
% 51.48/7.02      | sK0 != k1_tsep_1(sK0,sK2,sK3)
% 51.48/7.02      | sK0 != sK0 ),
% 51.48/7.02      inference(instantiation,[status(thm)],[c_1672]) ).
% 51.48/7.02  
% 51.48/7.02  cnf(contradiction,plain,
% 51.48/7.02      ( $false ),
% 51.48/7.02      inference(minisat,
% 51.48/7.02                [status(thm)],
% 51.48/7.02                [c_125968,c_50754,c_19728,c_19727,c_19726,c_3967,c_3966,
% 51.48/7.02                 c_3965,c_1964,c_1674,c_1578,c_284,c_351,c_18,c_19,c_20,
% 51.48/7.02                 c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30,c_31]) ).
% 51.48/7.02  
% 51.48/7.02  
% 51.48/7.02  % SZS output end CNFRefutation for theBenchmark.p
% 51.48/7.02  
% 51.48/7.02  ------                               Statistics
% 51.48/7.02  
% 51.48/7.02  ------ Selected
% 51.48/7.02  
% 51.48/7.02  total_time:                             6.277
% 51.48/7.02  
%------------------------------------------------------------------------------
