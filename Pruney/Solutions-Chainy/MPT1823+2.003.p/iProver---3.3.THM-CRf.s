%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:23 EST 2020

% Result     : Theorem 51.94s
% Output     : CNFRefutation 51.94s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1486)

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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39,f38,f37,f36])).

fof(f68,plain,(
    k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f41])).

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
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f48,plain,(
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

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f47,plain,(
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

fof(f53,plain,(
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

fof(f57,plain,(
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

fof(f42,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f72,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f44,plain,(
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
     => r1_funct_2(X0,X1,X2,X3,X4,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
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
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

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

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f49])).

cnf(c_286,plain,
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
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_119051,plain,
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
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_138545,plain,
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
    inference(instantiation,[status(thm)],[c_119051])).

cnf(c_20,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_275,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_287,plain,
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
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_888,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_5290,plain,
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
    inference(superposition,[status(thm)],[c_275,c_888])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_31,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_33,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_37,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_38,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_39,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_40,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5295,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_5290,c_31,c_32,c_33,c_37,c_38,c_39,c_40])).

cnf(c_5296,plain,
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
    inference(renaming,[status(thm)],[c_5295])).

cnf(c_272,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_902,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_278,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_897,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_289,plain,
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
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_886,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_2542,plain,
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
    inference(superposition,[status(thm)],[c_897,c_886])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_34,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_36,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_42,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3237,plain,
    ( v2_struct_0(X1_52) = iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2542,c_34,c_35,c_36,c_41,c_42,c_43,c_1486])).

cnf(c_3238,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(X0_52,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3237])).

cnf(c_3251,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_3238])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f47])).

cnf(c_290,plain,
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
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_885,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_290])).

cnf(c_2345,plain,
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
    inference(superposition,[status(thm)],[c_897,c_885])).

cnf(c_2350,plain,
    ( m1_pre_topc(X0_52,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2345,c_31,c_32,c_33,c_34,c_35,c_36,c_41,c_42])).

cnf(c_2351,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
    | m1_pre_topc(X0_52,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2350])).

cnf(c_2359,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_902,c_2351])).

cnf(c_3291,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3251,c_2359])).

cnf(c_297,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_341,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_285,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(X2_52,X1_52)
    | m1_pre_topc(k1_tsep_1(X1_52,X2_52,X0_52),X1_52)
    | v2_struct_0(X0_52)
    | v2_struct_0(X2_52)
    | v2_struct_0(X1_52)
    | ~ l1_pre_topc(X1_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1423,plain,
    ( ~ m1_pre_topc(X0_52,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK2,X0_52),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_1516,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_1517,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1516])).

cnf(c_317,plain,
    ( ~ m1_pre_topc(X0_52,X1_52)
    | m1_pre_topc(X2_52,X3_52)
    | X2_52 != X0_52
    | X3_52 != X1_52 ),
    theory(equality)).

cnf(c_1628,plain,
    ( m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | X0_52 != k1_tsep_1(sK0,sK2,sK3)
    | X1_52 != sK0 ),
    inference(instantiation,[status(thm)],[c_317])).

cnf(c_1629,plain,
    ( X0_52 != k1_tsep_1(sK0,sK2,sK3)
    | X1_52 != sK0
    | m1_pre_topc(X0_52,X1_52) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1628])).

cnf(c_1631,plain,
    ( sK0 != k1_tsep_1(sK0,sK2,sK3)
    | sK0 != sK0
    | m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1629])).

cnf(c_302,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1915,plain,
    ( X0_52 != X1_52
    | X0_52 = k1_tsep_1(sK0,sK2,sK3)
    | k1_tsep_1(sK0,sK2,sK3) != X1_52 ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_1916,plain,
    ( k1_tsep_1(sK0,sK2,sK3) != sK0
    | sK0 = k1_tsep_1(sK0,sK2,sK3)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_4001,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3291,c_31,c_32,c_33,c_37,c_38,c_39,c_40,c_341,c_275,c_1517,c_1631,c_1916])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_280,plain,
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
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_895,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_280])).

cnf(c_4678,plain,
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
    inference(superposition,[status(thm)],[c_275,c_895])).

cnf(c_4681,plain,
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
    inference(light_normalisation,[status(thm)],[c_4678,c_275])).

cnf(c_4791,plain,
    ( l1_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4681,c_31,c_32,c_33,c_37,c_38,c_39,c_40])).

cnf(c_4792,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_4791])).

cnf(c_4804,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_4792])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5390,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4804,c_34,c_35,c_36,c_41,c_42,c_43])).

cnf(c_7,plain,
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
    inference(cnf_transformation,[],[f51])).

cnf(c_288,plain,
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
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_887,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_4209,plain,
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
    inference(superposition,[status(thm)],[c_275,c_887])).

cnf(c_4807,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4209,c_31,c_32,c_33,c_37,c_38,c_39,c_40])).

cnf(c_4808,plain,
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
    inference(renaming,[status(thm)],[c_4807])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_294,plain,
    ( ~ r2_funct_2(X0_54,X1_54,X0_53,X1_53)
    | ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ v1_funct_2(X1_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | X0_53 = X1_53 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_881,plain,
    ( X0_53 = X1_53
    | r2_funct_2(X0_54,X1_54,X0_53,X1_53) != iProver_top
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(X1_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_1945,plain,
    ( sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_881])).

cnf(c_2189,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1945,c_41,c_42])).

cnf(c_2190,plain,
    ( sK4 = X0_53
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2189])).

cnf(c_4831,plain,
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
    inference(superposition,[status(thm)],[c_4808,c_2190])).

cnf(c_5459,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_4831,c_34,c_35,c_36])).

cnf(c_5460,plain,
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
    inference(renaming,[status(thm)],[c_5459])).

cnf(c_5476,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5390,c_5460])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f56])).

cnf(c_283,plain,
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
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_892,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_4004,plain,
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
    inference(superposition,[status(thm)],[c_4001,c_892])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f55])).

cnf(c_282,plain,
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
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_893,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_4005,plain,
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
    inference(superposition,[status(thm)],[c_4001,c_893])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f54])).

cnf(c_281,plain,
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
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_894,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_2602,plain,
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
    inference(superposition,[status(thm)],[c_897,c_894])).

cnf(c_3224,plain,
    ( v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | l1_pre_topc(X1_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2602,c_34,c_35,c_36,c_41,c_42])).

cnf(c_3225,plain,
    ( m1_pre_topc(X0_52,X1_52) != iProver_top
    | m1_pre_topc(sK0,X1_52) != iProver_top
    | v2_pre_topc(X1_52) != iProver_top
    | v2_struct_0(X1_52) = iProver_top
    | l1_pre_topc(X1_52) != iProver_top
    | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3224])).

cnf(c_4006,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4001,c_3225])).

cnf(c_1462,plain,
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
    inference(instantiation,[status(thm)],[c_282])).

cnf(c_15676,plain,
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
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_15681,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_15676])).

cnf(c_15683,plain,
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
    inference(instantiation,[status(thm)],[c_15681])).

cnf(c_1447,plain,
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
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_24600,plain,
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
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_24601,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_24600])).

cnf(c_24603,plain,
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
    inference(instantiation,[status(thm)],[c_24601])).

cnf(c_2410,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_52,X1_52)
    | ~ m1_pre_topc(sK0,X1_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X1_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X1_52)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_28103,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,X0_52)
    | ~ m1_pre_topc(sK0,X0_52)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k3_tmap_1(X0_52,sK1,sK0,sK3,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X0_52)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X0_52)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_52)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_53) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_28106,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,X0_52) != iProver_top
    | m1_pre_topc(sK0,X0_52) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(X0_52,sK1,sK0,sK3,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
    | v2_pre_topc(X0_52) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X0_52) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_52) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28103])).

cnf(c_28108,plain,
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
    inference(instantiation,[status(thm)],[c_28106])).

cnf(c_55842,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5476,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_341,c_275,c_1517,c_1631,c_1916,c_4004,c_4005,c_4006,c_15683,c_24603,c_28108])).

cnf(c_274,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_900,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_3250,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_3238])).

cnf(c_2358,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_900,c_2351])).

cnf(c_3304,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3250,c_2358])).

cnf(c_21051,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3304,c_31,c_32,c_33,c_37,c_38,c_39,c_40,c_341,c_275,c_1517,c_1631,c_1916])).

cnf(c_55846,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_55842,c_21051])).

cnf(c_16,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_311,plain,
    ( u1_struct_0(X0_52) = u1_struct_0(X1_52)
    | X0_52 != X1_52 ),
    theory(equality)).

cnf(c_329,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_298,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_342,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_293,plain,
    ( ~ l1_pre_topc(X0_52)
    | l1_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_270,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1536,plain,
    ( l1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_293,c_270])).

cnf(c_4,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X5,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_291,plain,
    ( r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X0_53)
    | ~ v1_funct_2(X1_53,X2_54,X3_54)
    | ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54)))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X3_54)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1452,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_54,X1_54,sK4,sK4)
    | ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(X1_54)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_1573,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_299,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_1875,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_3,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_292,plain,
    ( v2_struct_0(X0_52)
    | ~ v1_xboole_0(u1_struct_0(X0_52))
    | ~ l1_struct_0(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2651,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1570,plain,
    ( u1_struct_0(X0_52) = u1_struct_0(sK0)
    | X0_52 != sK0 ),
    inference(instantiation,[status(thm)],[c_311])).

cnf(c_5906,plain,
    ( u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)) = u1_struct_0(sK0)
    | k1_tsep_1(X0_52,X1_52,X2_52) != sK0 ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_7105,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) = u1_struct_0(sK0)
    | k1_tsep_1(sK0,sK2,sK3) != sK0 ),
    inference(instantiation,[status(thm)],[c_5906])).

cnf(c_314,plain,
    ( ~ r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X1_53)
    | r1_funct_2(X4_54,X5_54,X6_54,X7_54,X2_53,X3_53)
    | X4_54 != X0_54
    | X5_54 != X1_54
    | X6_54 != X2_54
    | X7_54 != X3_54
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_1660,plain,
    ( r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | X1_54 != u1_struct_0(sK1)
    | X3_54 != u1_struct_0(sK1)
    | X0_54 != u1_struct_0(sK0)
    | X2_54 != u1_struct_0(sK0)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_2326,plain,
    ( r1_funct_2(X0_54,X1_54,X2_54,u1_struct_0(sK1),X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | X1_54 != u1_struct_0(sK1)
    | X0_54 != u1_struct_0(sK0)
    | X2_54 != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_4163,plain,
    ( r1_funct_2(X0_54,u1_struct_0(sK1),X1_54,u1_struct_0(sK1),X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | X0_54 != u1_struct_0(sK0)
    | X1_54 != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_2326])).

cnf(c_8512,plain,
    ( r1_funct_2(X0_54,u1_struct_0(sK1),u1_struct_0(X0_52),u1_struct_0(sK1),X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | X0_54 != u1_struct_0(sK0)
    | u1_struct_0(X0_52) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_4163])).

cnf(c_10859,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X0_52),u1_struct_0(sK1),X0_53,X1_53)
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | u1_struct_0(X0_52) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | X0_53 != sK4
    | X1_53 != sK4 ),
    inference(instantiation,[status(thm)],[c_8512])).

cnf(c_14724,plain,
    ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK0) != u1_struct_0(sK0)
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_10859])).

cnf(c_55851,plain,
    ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55846,c_27,c_19,c_18,c_17,c_16,c_329,c_341,c_342,c_275,c_1536,c_1573,c_1875,c_2651,c_7105,c_14724])).

cnf(c_55855,plain,
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
    inference(superposition,[status(thm)],[c_5296,c_55851])).

cnf(c_55856,plain,
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
    inference(predicate_to_equality_rev,[status(thm)],[c_55855])).

cnf(c_21059,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21051,c_3225])).

cnf(c_21270,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_21059])).

cnf(c_21057,plain,
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
    inference(superposition,[status(thm)],[c_21051,c_893])).

cnf(c_21269,plain,
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
    inference(predicate_to_equality_rev,[status(thm)],[c_21057])).

cnf(c_21056,plain,
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
    inference(superposition,[status(thm)],[c_21051,c_892])).

cnf(c_21268,plain,
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
    inference(predicate_to_equality_rev,[status(thm)],[c_21056])).

cnf(c_4069,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK0,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4006])).

cnf(c_4068,plain,
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
    inference(predicate_to_equality_rev,[status(thm)],[c_4005])).

cnf(c_4067,plain,
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
    inference(predicate_to_equality_rev,[status(thm)],[c_4004])).

cnf(c_1630,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
    | m1_pre_topc(sK0,sK0)
    | sK0 != k1_tsep_1(sK0,sK2,sK3)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_138545,c_55856,c_21270,c_21269,c_21268,c_4069,c_4068,c_4067,c_1916,c_1630,c_1516,c_275,c_341,c_17,c_18,c_19,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:33:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.94/6.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.94/6.98  
% 51.94/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.94/6.98  
% 51.94/6.98  ------  iProver source info
% 51.94/6.98  
% 51.94/6.98  git: date: 2020-06-30 10:37:57 +0100
% 51.94/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.94/6.98  git: non_committed_changes: false
% 51.94/6.98  git: last_make_outside_of_git: false
% 51.94/6.98  
% 51.94/6.98  ------ 
% 51.94/6.98  ------ Parsing...
% 51.94/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.94/6.98  
% 51.94/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 51.94/6.98  
% 51.94/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.94/6.98  
% 51.94/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.94/6.98  ------ Proving...
% 51.94/6.98  ------ Problem Properties 
% 51.94/6.98  
% 51.94/6.98  
% 51.94/6.98  clauses                                 31
% 51.94/6.98  conjectures                             15
% 51.94/6.98  EPR                                     12
% 51.94/6.98  Horn                                    19
% 51.94/6.98  unary                                   15
% 51.94/6.98  binary                                  1
% 51.94/6.98  lits                                    180
% 51.94/6.98  lits eq                                 4
% 51.94/6.98  fd_pure                                 0
% 51.94/6.98  fd_pseudo                               0
% 51.94/6.98  fd_cond                                 0
% 51.94/6.98  fd_pseudo_cond                          1
% 51.94/6.98  AC symbols                              0
% 51.94/6.98  
% 51.94/6.98  ------ Input Options Time Limit: Unbounded
% 51.94/6.98  
% 51.94/6.98  
% 51.94/6.98  ------ 
% 51.94/6.98  Current options:
% 51.94/6.98  ------ 
% 51.94/6.98  
% 51.94/6.98  
% 51.94/6.98  
% 51.94/6.98  
% 51.94/6.98  ------ Proving...
% 51.94/6.98  
% 51.94/6.98  
% 51.94/6.98  % SZS status Theorem for theBenchmark.p
% 51.94/6.98  
% 51.94/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 51.94/6.98  
% 51.94/6.98  fof(f7,axiom,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f25,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.94/6.98    inference(ennf_transformation,[],[f7])).
% 51.94/6.98  
% 51.94/6.98  fof(f26,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.94/6.98    inference(flattening,[],[f25])).
% 51.94/6.98  
% 51.94/6.98  fof(f49,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f26])).
% 51.94/6.98  
% 51.94/6.98  fof(f11,conjecture,(
% 51.94/6.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f12,negated_conjecture,(
% 51.94/6.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 51.94/6.98    inference(negated_conjecture,[],[f11])).
% 51.94/6.98  
% 51.94/6.98  fof(f33,plain,(
% 51.94/6.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 51.94/6.98    inference(ennf_transformation,[],[f12])).
% 51.94/6.98  
% 51.94/6.98  fof(f34,plain,(
% 51.94/6.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 51.94/6.98    inference(flattening,[],[f33])).
% 51.94/6.98  
% 51.94/6.98  fof(f40,plain,(
% 51.94/6.98    ( ! [X2,X0,X3,X1] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),sK4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,sK4,X2),k2_tmap_1(X0,X1,sK4,X3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 51.94/6.98    introduced(choice_axiom,[])).
% 51.94/6.98  
% 51.94/6.98  fof(f39,plain,(
% 51.94/6.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,sK3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,sK3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,sK3) = X0 & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 51.94/6.98    introduced(choice_axiom,[])).
% 51.94/6.98  
% 51.94/6.98  fof(f38,plain,(
% 51.94/6.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,sK2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,sK2,X3,k2_tmap_1(X0,X1,X4,sK2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,sK2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 51.94/6.98    introduced(choice_axiom,[])).
% 51.94/6.98  
% 51.94/6.98  fof(f37,plain,(
% 51.94/6.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(X0,sK1,X2,X3,k2_tmap_1(X0,sK1,X4,X2),k2_tmap_1(X0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 51.94/6.98    introduced(choice_axiom,[])).
% 51.94/6.98  
% 51.94/6.98  fof(f36,plain,(
% 51.94/6.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(sK0,X2,X3) = sK0 & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 51.94/6.98    introduced(choice_axiom,[])).
% 51.94/6.98  
% 51.94/6.98  fof(f41,plain,(
% 51.94/6.98    ((((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & k1_tsep_1(sK0,sK2,sK3) = sK0 & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 51.94/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f40,f39,f38,f37,f36])).
% 51.94/6.98  
% 51.94/6.98  fof(f68,plain,(
% 51.94/6.98    k1_tsep_1(sK0,sK2,sK3) = sK0),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f50,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f26])).
% 51.94/6.98  
% 51.94/6.98  fof(f58,plain,(
% 51.94/6.98    ~v2_struct_0(sK0)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f59,plain,(
% 51.94/6.98    v2_pre_topc(sK0)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f60,plain,(
% 51.94/6.98    l1_pre_topc(sK0)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f64,plain,(
% 51.94/6.98    ~v2_struct_0(sK2)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f65,plain,(
% 51.94/6.98    m1_pre_topc(sK2,sK0)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f66,plain,(
% 51.94/6.98    ~v2_struct_0(sK3)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f67,plain,(
% 51.94/6.98    m1_pre_topc(sK3,sK0)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f71,plain,(
% 51.94/6.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f6,axiom,(
% 51.94/6.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f23,plain,(
% 51.94/6.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.94/6.98    inference(ennf_transformation,[],[f6])).
% 51.94/6.98  
% 51.94/6.98  fof(f24,plain,(
% 51.94/6.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.94/6.98    inference(flattening,[],[f23])).
% 51.94/6.98  
% 51.94/6.98  fof(f48,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f24])).
% 51.94/6.98  
% 51.94/6.98  fof(f61,plain,(
% 51.94/6.98    ~v2_struct_0(sK1)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f62,plain,(
% 51.94/6.98    v2_pre_topc(sK1)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f63,plain,(
% 51.94/6.98    l1_pre_topc(sK1)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f69,plain,(
% 51.94/6.98    v1_funct_1(sK4)),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f70,plain,(
% 51.94/6.98    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f5,axiom,(
% 51.94/6.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f21,plain,(
% 51.94/6.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.94/6.98    inference(ennf_transformation,[],[f5])).
% 51.94/6.98  
% 51.94/6.98  fof(f22,plain,(
% 51.94/6.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.94/6.98    inference(flattening,[],[f21])).
% 51.94/6.98  
% 51.94/6.98  fof(f47,plain,(
% 51.94/6.98    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f22])).
% 51.94/6.98  
% 51.94/6.98  fof(f8,axiom,(
% 51.94/6.98    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f13,plain,(
% 51.94/6.98    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 51.94/6.98    inference(pure_predicate_removal,[],[f8])).
% 51.94/6.98  
% 51.94/6.98  fof(f27,plain,(
% 51.94/6.98    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 51.94/6.98    inference(ennf_transformation,[],[f13])).
% 51.94/6.98  
% 51.94/6.98  fof(f28,plain,(
% 51.94/6.98    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 51.94/6.98    inference(flattening,[],[f27])).
% 51.94/6.98  
% 51.94/6.98  fof(f53,plain,(
% 51.94/6.98    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f28])).
% 51.94/6.98  
% 51.94/6.98  fof(f10,axiom,(
% 51.94/6.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f31,plain,(
% 51.94/6.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.94/6.98    inference(ennf_transformation,[],[f10])).
% 51.94/6.98  
% 51.94/6.98  fof(f32,plain,(
% 51.94/6.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.94/6.98    inference(flattening,[],[f31])).
% 51.94/6.98  
% 51.94/6.98  fof(f57,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f32])).
% 51.94/6.98  
% 51.94/6.98  fof(f51,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f26])).
% 51.94/6.98  
% 51.94/6.98  fof(f1,axiom,(
% 51.94/6.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f14,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 51.94/6.98    inference(ennf_transformation,[],[f1])).
% 51.94/6.98  
% 51.94/6.98  fof(f15,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.94/6.98    inference(flattening,[],[f14])).
% 51.94/6.98  
% 51.94/6.98  fof(f35,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.94/6.98    inference(nnf_transformation,[],[f15])).
% 51.94/6.98  
% 51.94/6.98  fof(f42,plain,(
% 51.94/6.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f35])).
% 51.94/6.98  
% 51.94/6.98  fof(f9,axiom,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f29,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 51.94/6.98    inference(ennf_transformation,[],[f9])).
% 51.94/6.98  
% 51.94/6.98  fof(f30,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 51.94/6.98    inference(flattening,[],[f29])).
% 51.94/6.98  
% 51.94/6.98  fof(f56,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f30])).
% 51.94/6.98  
% 51.94/6.98  fof(f55,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f30])).
% 51.94/6.98  
% 51.94/6.98  fof(f54,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f30])).
% 51.94/6.98  
% 51.94/6.98  fof(f72,plain,(
% 51.94/6.98    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 51.94/6.98    inference(cnf_transformation,[],[f41])).
% 51.94/6.98  
% 51.94/6.98  fof(f2,axiom,(
% 51.94/6.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f16,plain,(
% 51.94/6.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 51.94/6.98    inference(ennf_transformation,[],[f2])).
% 51.94/6.98  
% 51.94/6.98  fof(f44,plain,(
% 51.94/6.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f16])).
% 51.94/6.98  
% 51.94/6.98  fof(f4,axiom,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => r1_funct_2(X0,X1,X2,X3,X4,X4))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f19,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 51.94/6.98    inference(ennf_transformation,[],[f4])).
% 51.94/6.98  
% 51.94/6.98  fof(f20,plain,(
% 51.94/6.98    ! [X0,X1,X2,X3,X4,X5] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 51.94/6.98    inference(flattening,[],[f19])).
% 51.94/6.98  
% 51.94/6.98  fof(f46,plain,(
% 51.94/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f20])).
% 51.94/6.98  
% 51.94/6.98  fof(f3,axiom,(
% 51.94/6.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 51.94/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.94/6.98  
% 51.94/6.98  fof(f17,plain,(
% 51.94/6.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 51.94/6.98    inference(ennf_transformation,[],[f3])).
% 51.94/6.98  
% 51.94/6.98  fof(f18,plain,(
% 51.94/6.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 51.94/6.98    inference(flattening,[],[f17])).
% 51.94/6.98  
% 51.94/6.98  fof(f45,plain,(
% 51.94/6.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 51.94/6.98    inference(cnf_transformation,[],[f18])).
% 51.94/6.98  
% 51.94/6.98  cnf(c_9,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.94/6.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 51.94/6.98      | ~ m1_pre_topc(X4,X5)
% 51.94/6.98      | ~ m1_pre_topc(X1,X5)
% 51.94/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.94/6.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 51.94/6.98      | ~ v2_pre_topc(X2)
% 51.94/6.98      | ~ v2_pre_topc(X5)
% 51.94/6.98      | v2_struct_0(X5)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | v2_struct_0(X4)
% 51.94/6.98      | v2_struct_0(X1)
% 51.94/6.98      | ~ l1_pre_topc(X5)
% 51.94/6.98      | ~ l1_pre_topc(X2)
% 51.94/6.98      | ~ v1_funct_1(X3)
% 51.94/6.98      | ~ v1_funct_1(X0)
% 51.94/6.98      | v1_funct_1(k10_tmap_1(X5,X2,X1,X4,X0,X3)) ),
% 51.94/6.98      inference(cnf_transformation,[],[f49]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_286,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X3_52)
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X3_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ v2_pre_topc(X3_52)
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(X3_52)
% 51.94/6.98      | v2_struct_0(X2_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X3_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | ~ v1_funct_1(X1_53)
% 51.94/6.98      | v1_funct_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53)) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_9]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_119051,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_2(X1_53,u1_struct_0(X1_52),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X2_52)
% 51.94/6.98      | ~ m1_pre_topc(X1_52,X2_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
% 51.94/6.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_52),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(X2_52)
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(X2_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | ~ l1_pre_topc(X2_52)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | ~ v1_funct_1(X1_53)
% 51.94/6.98      | v1_funct_1(k10_tmap_1(X2_52,sK1,X0_52,X1_52,X0_53,X1_53)) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_286]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_138545,plain,
% 51.94/6.98      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(sK3,sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK2,sK0)
% 51.94/6.98      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 51.94/6.98      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | ~ v2_pre_topc(sK0)
% 51.94/6.98      | v2_struct_0(sK3)
% 51.94/6.98      | v2_struct_0(sK2)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ l1_pre_topc(sK0)
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 51.94/6.98      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 51.94/6.98      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_119051]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_20,negated_conjecture,
% 51.94/6.98      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 51.94/6.98      inference(cnf_transformation,[],[f68]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_275,negated_conjecture,
% 51.94/6.98      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_20]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_8,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.94/6.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 51.94/6.98      | v1_funct_2(k10_tmap_1(X5,X2,X1,X4,X0,X3),u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))
% 51.94/6.98      | ~ m1_pre_topc(X4,X5)
% 51.94/6.98      | ~ m1_pre_topc(X1,X5)
% 51.94/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.94/6.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 51.94/6.98      | ~ v2_pre_topc(X2)
% 51.94/6.98      | ~ v2_pre_topc(X5)
% 51.94/6.98      | v2_struct_0(X5)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | v2_struct_0(X4)
% 51.94/6.98      | v2_struct_0(X1)
% 51.94/6.98      | ~ l1_pre_topc(X5)
% 51.94/6.98      | ~ l1_pre_topc(X2)
% 51.94/6.98      | ~ v1_funct_1(X3)
% 51.94/6.98      | ~ v1_funct_1(X0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f50]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_287,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 51.94/6.98      | v1_funct_2(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52))
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X3_52)
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X3_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ v2_pre_topc(X3_52)
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(X3_52)
% 51.94/6.98      | v2_struct_0(X2_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X3_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | ~ v1_funct_1(X1_53) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_8]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_888,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52)) = iProver_top
% 51.94/6.98      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X3_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X2_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5290,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK3) = iProver_top
% 51.94/6.98      | v2_struct_0(sK2) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_275,c_888]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_30,negated_conjecture,
% 51.94/6.98      ( ~ v2_struct_0(sK0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f58]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_31,plain,
% 51.94/6.98      ( v2_struct_0(sK0) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_29,negated_conjecture,
% 51.94/6.98      ( v2_pre_topc(sK0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f59]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_32,plain,
% 51.94/6.98      ( v2_pre_topc(sK0) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_28,negated_conjecture,
% 51.94/6.98      ( l1_pre_topc(sK0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f60]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_33,plain,
% 51.94/6.98      ( l1_pre_topc(sK0) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_24,negated_conjecture,
% 51.94/6.98      ( ~ v2_struct_0(sK2) ),
% 51.94/6.98      inference(cnf_transformation,[],[f64]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_37,plain,
% 51.94/6.98      ( v2_struct_0(sK2) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_23,negated_conjecture,
% 51.94/6.98      ( m1_pre_topc(sK2,sK0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f65]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_38,plain,
% 51.94/6.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_22,negated_conjecture,
% 51.94/6.98      ( ~ v2_struct_0(sK3) ),
% 51.94/6.98      inference(cnf_transformation,[],[f66]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_39,plain,
% 51.94/6.98      ( v2_struct_0(sK3) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_21,negated_conjecture,
% 51.94/6.98      ( m1_pre_topc(sK3,sK0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f67]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_40,plain,
% 51.94/6.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5295,plain,
% 51.94/6.98      ( l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_5290,c_31,c_32,c_33,c_37,c_38,c_39,c_40]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5296,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),u1_struct_0(sK0),u1_struct_0(X0_52)) = iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top ),
% 51.94/6.98      inference(renaming,[status(thm)],[c_5295]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_272,negated_conjecture,
% 51.94/6.98      ( m1_pre_topc(sK2,sK0) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_23]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_902,plain,
% 51.94/6.98      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_17,negated_conjecture,
% 51.94/6.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 51.94/6.98      inference(cnf_transformation,[],[f71]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_278,negated_conjecture,
% 51.94/6.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_17]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_897,plain,
% 51.94/6.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_6,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.94/6.98      | ~ m1_pre_topc(X3,X4)
% 51.94/6.98      | ~ m1_pre_topc(X3,X1)
% 51.94/6.98      | ~ m1_pre_topc(X1,X4)
% 51.94/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.94/6.98      | ~ v2_pre_topc(X2)
% 51.94/6.98      | ~ v2_pre_topc(X4)
% 51.94/6.98      | v2_struct_0(X4)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | ~ l1_pre_topc(X4)
% 51.94/6.98      | ~ l1_pre_topc(X2)
% 51.94/6.98      | ~ v1_funct_1(X0)
% 51.94/6.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f48]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_289,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X0_52)
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X3_52)
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X3_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ v2_pre_topc(X3_52)
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | v2_struct_0(X3_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X3_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_6]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_886,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X3_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2542,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 51.94/6.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_897,c_886]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_27,negated_conjecture,
% 51.94/6.98      ( ~ v2_struct_0(sK1) ),
% 51.94/6.98      inference(cnf_transformation,[],[f61]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_34,plain,
% 51.94/6.98      ( v2_struct_0(sK1) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_26,negated_conjecture,
% 51.94/6.98      ( v2_pre_topc(sK1) ),
% 51.94/6.98      inference(cnf_transformation,[],[f62]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_35,plain,
% 51.94/6.98      ( v2_pre_topc(sK1) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_25,negated_conjecture,
% 51.94/6.98      ( l1_pre_topc(sK1) ),
% 51.94/6.98      inference(cnf_transformation,[],[f63]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_36,plain,
% 51.94/6.98      ( l1_pre_topc(sK1) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_19,negated_conjecture,
% 51.94/6.98      ( v1_funct_1(sK4) ),
% 51.94/6.98      inference(cnf_transformation,[],[f69]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_41,plain,
% 51.94/6.98      ( v1_funct_1(sK4) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_18,negated_conjecture,
% 51.94/6.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 51.94/6.98      inference(cnf_transformation,[],[f70]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_42,plain,
% 51.94/6.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3237,plain,
% 51.94/6.98      ( v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 51.94/6.98      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_2542,c_34,c_35,c_36,c_41,c_42,c_43,c_1486]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3238,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)
% 51.94/6.98      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top ),
% 51.94/6.98      inference(renaming,[status(thm)],[c_3237]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3251,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_902,c_3238]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.94/6.98      | ~ m1_pre_topc(X3,X1)
% 51.94/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.94/6.98      | ~ v2_pre_topc(X2)
% 51.94/6.98      | ~ v2_pre_topc(X1)
% 51.94/6.98      | v2_struct_0(X1)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | ~ l1_pre_topc(X1)
% 51.94/6.98      | ~ l1_pre_topc(X2)
% 51.94/6.98      | ~ v1_funct_1(X0)
% 51.94/6.98      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 51.94/6.98      inference(cnf_transformation,[],[f47]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_290,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X0_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ v2_pre_topc(X0_52)
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X0_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_5]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_885,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(X0_52),u1_struct_0(X1_52),X0_53,u1_struct_0(X2_52)) = k2_tmap_1(X0_52,X1_52,X0_53,X2_52)
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2345,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
% 51.94/6.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,sK0) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_897,c_885]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2350,plain,
% 51.94/6.98      ( m1_pre_topc(X0_52,sK0) != iProver_top
% 51.94/6.98      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52) ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_2345,c_31,c_32,c_33,c_34,c_35,c_36,c_41,c_42]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2351,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_52)) = k2_tmap_1(sK0,sK1,sK4,X0_52)
% 51.94/6.98      | m1_pre_topc(X0_52,sK0) != iProver_top ),
% 51.94/6.98      inference(renaming,[status(thm)],[c_2350]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2359,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_902,c_2351]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3291,plain,
% 51.94/6.98      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.94/6.98      inference(light_normalisation,[status(thm)],[c_3251,c_2359]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_297,plain,( X0_52 = X0_52 ),theory(equality) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_341,plain,
% 51.94/6.98      ( sK0 = sK0 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_297]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_10,plain,
% 51.94/6.98      ( ~ m1_pre_topc(X0,X1)
% 51.94/6.98      | ~ m1_pre_topc(X2,X1)
% 51.94/6.98      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 51.94/6.98      | v2_struct_0(X1)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | v2_struct_0(X0)
% 51.94/6.98      | ~ l1_pre_topc(X1) ),
% 51.94/6.98      inference(cnf_transformation,[],[f53]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_285,plain,
% 51.94/6.98      ( ~ m1_pre_topc(X0_52,X1_52)
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X1_52)
% 51.94/6.98      | m1_pre_topc(k1_tsep_1(X1_52,X2_52,X0_52),X1_52)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(X2_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_10]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1423,plain,
% 51.94/6.98      ( ~ m1_pre_topc(X0_52,sK0)
% 51.94/6.98      | m1_pre_topc(k1_tsep_1(sK0,sK2,X0_52),sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK2,sK0)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(sK2)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK0) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_285]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1516,plain,
% 51.94/6.98      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK3,sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK2,sK0)
% 51.94/6.98      | v2_struct_0(sK3)
% 51.94/6.98      | v2_struct_0(sK2)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK0) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1423]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1517,plain,
% 51.94/6.98      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) = iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK3) = iProver_top
% 51.94/6.98      | v2_struct_0(sK2) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_1516]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_317,plain,
% 51.94/6.98      ( ~ m1_pre_topc(X0_52,X1_52)
% 51.94/6.98      | m1_pre_topc(X2_52,X3_52)
% 51.94/6.98      | X2_52 != X0_52
% 51.94/6.98      | X3_52 != X1_52 ),
% 51.94/6.98      theory(equality) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1628,plain,
% 51.94/6.98      ( m1_pre_topc(X0_52,X1_52)
% 51.94/6.98      | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
% 51.94/6.98      | X0_52 != k1_tsep_1(sK0,sK2,sK3)
% 51.94/6.98      | X1_52 != sK0 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_317]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1629,plain,
% 51.94/6.98      ( X0_52 != k1_tsep_1(sK0,sK2,sK3)
% 51.94/6.98      | X1_52 != sK0
% 51.94/6.98      | m1_pre_topc(X0_52,X1_52) = iProver_top
% 51.94/6.98      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_1628]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1631,plain,
% 51.94/6.98      ( sK0 != k1_tsep_1(sK0,sK2,sK3)
% 51.94/6.98      | sK0 != sK0
% 51.94/6.98      | m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) = iProver_top ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1629]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_302,plain,
% 51.94/6.98      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 51.94/6.98      theory(equality) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1915,plain,
% 51.94/6.98      ( X0_52 != X1_52
% 51.94/6.98      | X0_52 = k1_tsep_1(sK0,sK2,sK3)
% 51.94/6.98      | k1_tsep_1(sK0,sK2,sK3) != X1_52 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_302]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1916,plain,
% 51.94/6.98      ( k1_tsep_1(sK0,sK2,sK3) != sK0
% 51.94/6.98      | sK0 = k1_tsep_1(sK0,sK2,sK3)
% 51.94/6.98      | sK0 != sK0 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1915]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4001,plain,
% 51.94/6.98      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_3291,c_31,c_32,c_33,c_37,c_38,c_39,c_40,c_341,c_275,
% 51.94/6.98                 c_1517,c_1631,c_1916]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_15,plain,
% 51.94/6.98      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
% 51.94/6.98      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
% 51.94/6.98      | ~ m1_pre_topc(X2,X0)
% 51.94/6.98      | ~ m1_pre_topc(X1,X0)
% 51.94/6.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
% 51.94/6.98      | ~ v2_pre_topc(X3)
% 51.94/6.98      | ~ v2_pre_topc(X0)
% 51.94/6.98      | v2_struct_0(X0)
% 51.94/6.98      | v2_struct_0(X3)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | v2_struct_0(X1)
% 51.94/6.98      | ~ l1_pre_topc(X0)
% 51.94/6.98      | ~ l1_pre_topc(X3)
% 51.94/6.98      | ~ v1_funct_1(X4) ),
% 51.94/6.98      inference(cnf_transformation,[],[f57]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_280,plain,
% 51.94/6.98      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52),X0_53,k10_tmap_1(X0_52,X3_52,X1_52,X2_52,k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X1_52,X0_53),k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X2_52,X0_53)))
% 51.94/6.98      | ~ v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X0_52)
% 51.94/6.98      | ~ m1_pre_topc(X1_52,X0_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52))))
% 51.94/6.98      | ~ v2_pre_topc(X3_52)
% 51.94/6.98      | ~ v2_pre_topc(X0_52)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(X3_52)
% 51.94/6.98      | v2_struct_0(X2_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X0_52)
% 51.94/6.98      | ~ l1_pre_topc(X3_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_15]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_895,plain,
% 51.94/6.98      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52),X0_53,k10_tmap_1(X0_52,X3_52,X1_52,X2_52,k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X1_52,X0_53),k3_tmap_1(X0_52,X3_52,k1_tsep_1(X0_52,X1_52,X2_52),X2_52,X0_53))) = iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X2_52,X0_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X1_52,X0_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)),u1_struct_0(X3_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X3_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X2_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_280]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4678,plain,
% 51.94/6.98      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK3) = iProver_top
% 51.94/6.98      | v2_struct_0(sK2) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_275,c_895]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4681,plain,
% 51.94/6.98      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK3) = iProver_top
% 51.94/6.98      | v2_struct_0(sK2) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(light_normalisation,[status(thm)],[c_4678,c_275]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4791,plain,
% 51.94/6.98      ( l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_4681,c_31,c_32,c_33,c_37,c_38,c_39,c_40]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4792,plain,
% 51.94/6.98      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_52),X0_53,k10_tmap_1(sK0,X0_52,sK2,sK3,k3_tmap_1(sK0,X0_52,sK0,sK2,X0_53),k3_tmap_1(sK0,X0_52,sK0,sK3,X0_53))) = iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(renaming,[status(thm)],[c_4791]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4804,plain,
% 51.94/6.98      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top
% 51.94/6.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_4001,c_4792]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_43,plain,
% 51.94/6.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5390,plain,
% 51.94/6.98      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_4804,c_34,c_35,c_36,c_41,c_42,c_43]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_7,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.94/6.98      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 51.94/6.98      | ~ m1_pre_topc(X4,X5)
% 51.94/6.98      | ~ m1_pre_topc(X1,X5)
% 51.94/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.94/6.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 51.94/6.98      | m1_subset_1(k10_tmap_1(X5,X2,X1,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))))
% 51.94/6.98      | ~ v2_pre_topc(X2)
% 51.94/6.98      | ~ v2_pre_topc(X5)
% 51.94/6.98      | v2_struct_0(X5)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | v2_struct_0(X4)
% 51.94/6.98      | v2_struct_0(X1)
% 51.94/6.98      | ~ l1_pre_topc(X5)
% 51.94/6.98      | ~ l1_pre_topc(X2)
% 51.94/6.98      | ~ v1_funct_1(X3)
% 51.94/6.98      | ~ v1_funct_1(X0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f51]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_288,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X3_52)
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X3_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 51.94/6.98      | m1_subset_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ v2_pre_topc(X3_52)
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(X3_52)
% 51.94/6.98      | v2_struct_0(X2_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X3_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | ~ v1_funct_1(X1_53) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_7]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_887,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(X2_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(k10_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53,X1_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_52,X0_52,X2_52)),u1_struct_0(X1_52)))) = iProver_top
% 51.94/6.98      | v2_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X3_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X2_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4209,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK3) = iProver_top
% 51.94/6.98      | v2_struct_0(sK2) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_275,c_887]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4807,plain,
% 51.94/6.98      ( l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_4209,c_31,c_32,c_33,c_37,c_38,c_39,c_40]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4808,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(sK3),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK2),u1_struct_0(X0_52)) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(k10_tmap_1(sK0,X0_52,sK2,sK3,X1_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_52)))) = iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top ),
% 51.94/6.98      inference(renaming,[status(thm)],[c_4807]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1,plain,
% 51.94/6.98      ( ~ r2_funct_2(X0,X1,X2,X3)
% 51.94/6.98      | ~ v1_funct_2(X3,X0,X1)
% 51.94/6.98      | ~ v1_funct_2(X2,X0,X1)
% 51.94/6.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.94/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.94/6.98      | ~ v1_funct_1(X3)
% 51.94/6.98      | ~ v1_funct_1(X2)
% 51.94/6.98      | X2 = X3 ),
% 51.94/6.98      inference(cnf_transformation,[],[f42]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_294,plain,
% 51.94/6.98      ( ~ r2_funct_2(X0_54,X1_54,X0_53,X1_53)
% 51.94/6.98      | ~ v1_funct_2(X0_53,X0_54,X1_54)
% 51.94/6.98      | ~ v1_funct_2(X1_53,X0_54,X1_54)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 51.94/6.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | ~ v1_funct_1(X1_53)
% 51.94/6.98      | X0_53 = X1_53 ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_1]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_881,plain,
% 51.94/6.98      ( X0_53 = X1_53
% 51.94/6.98      | r2_funct_2(X0_54,X1_54,X0_53,X1_53) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,X0_54,X1_54) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1945,plain,
% 51.94/6.98      ( sK4 = X0_53
% 51.94/6.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_897,c_881]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2189,plain,
% 51.94/6.98      ( v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | sK4 = X0_53
% 51.94/6.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_1945,c_41,c_42]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2190,plain,
% 51.94/6.98      ( sK4 = X0_53
% 51.94/6.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_53) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(renaming,[status(thm)],[c_2189]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4831,plain,
% 51.94/6.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
% 51.94/6.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_4808,c_2190]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5459,plain,
% 51.94/6.98      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
% 51.94/6.98      | k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_4831,c_34,c_35,c_36]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5460,plain,
% 51.94/6.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53) = sK4
% 51.94/6.98      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top
% 51.94/6.98      | v1_funct_2(X1_53,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(X0_53,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(X1_53) != iProver_top
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_53,X1_53)) != iProver_top ),
% 51.94/6.98      inference(renaming,[status(thm)],[c_5459]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5476,plain,
% 51.94/6.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 51.94/6.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 51.94/6.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_5390,c_5460]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_12,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.94/6.98      | ~ m1_pre_topc(X3,X4)
% 51.94/6.98      | ~ m1_pre_topc(X1,X4)
% 51.94/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.94/6.98      | m1_subset_1(k3_tmap_1(X4,X2,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 51.94/6.98      | ~ v2_pre_topc(X2)
% 51.94/6.98      | ~ v2_pre_topc(X4)
% 51.94/6.98      | v2_struct_0(X4)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | ~ l1_pre_topc(X4)
% 51.94/6.98      | ~ l1_pre_topc(X2)
% 51.94/6.98      | ~ v1_funct_1(X0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f56]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_283,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X3_52)
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X3_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.94/6.98      | m1_subset_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ v2_pre_topc(X3_52)
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | v2_struct_0(X3_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X3_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_12]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_892,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | m1_subset_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_52),u1_struct_0(X1_52)))) = iProver_top
% 51.94/6.98      | v2_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X3_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4004,plain,
% 51.94/6.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_4001,c_892]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_13,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.94/6.98      | v1_funct_2(k3_tmap_1(X3,X2,X1,X4,X0),u1_struct_0(X4),u1_struct_0(X2))
% 51.94/6.98      | ~ m1_pre_topc(X4,X3)
% 51.94/6.98      | ~ m1_pre_topc(X1,X3)
% 51.94/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.94/6.98      | ~ v2_pre_topc(X2)
% 51.94/6.98      | ~ v2_pre_topc(X3)
% 51.94/6.98      | v2_struct_0(X3)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | ~ l1_pre_topc(X3)
% 51.94/6.98      | ~ l1_pre_topc(X2)
% 51.94/6.98      | ~ v1_funct_1(X0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f55]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_282,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.94/6.98      | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ m1_pre_topc(X3_52,X2_52)
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X2_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ v2_pre_topc(X2_52)
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | v2_struct_0(X2_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X2_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_13]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_893,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | v1_funct_2(k3_tmap_1(X2_52,X1_52,X0_52,X3_52,X0_53),u1_struct_0(X3_52),u1_struct_0(X1_52)) = iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X2_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X3_52,X2_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X2_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X2_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X2_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4005,plain,
% 51.94/6.98      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 51.94/6.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_4001,c_893]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_14,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 51.94/6.98      | ~ m1_pre_topc(X3,X4)
% 51.94/6.98      | ~ m1_pre_topc(X1,X4)
% 51.94/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 51.94/6.98      | ~ v2_pre_topc(X2)
% 51.94/6.98      | ~ v2_pre_topc(X4)
% 51.94/6.98      | v2_struct_0(X4)
% 51.94/6.98      | v2_struct_0(X2)
% 51.94/6.98      | ~ l1_pre_topc(X4)
% 51.94/6.98      | ~ l1_pre_topc(X2)
% 51.94/6.98      | ~ v1_funct_1(X0)
% 51.94/6.98      | v1_funct_1(k3_tmap_1(X4,X2,X1,X3,X0)) ),
% 51.94/6.98      inference(cnf_transformation,[],[f54]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_281,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52))
% 51.94/6.98      | ~ m1_pre_topc(X2_52,X3_52)
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X3_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52))))
% 51.94/6.98      | ~ v2_pre_topc(X3_52)
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | v2_struct_0(X3_52)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(X3_52)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | v1_funct_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_14]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_894,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(X0_52),u1_struct_0(X1_52)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X2_52,X3_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X3_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(X1_52)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X3_52) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X3_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top
% 51.94/6.98      | v1_funct_1(k3_tmap_1(X3_52,X1_52,X0_52,X2_52,X0_53)) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2602,plain,
% 51.94/6.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_897,c_894]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3224,plain,
% 51.94/6.98      ( v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_2602,c_34,c_35,c_36,c_41,c_42]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3225,plain,
% 51.94/6.98      ( m1_pre_topc(X0_52,X1_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X1_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v2_struct_0(X1_52) = iProver_top
% 51.94/6.98      | l1_pre_topc(X1_52) != iProver_top
% 51.94/6.98      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4)) = iProver_top ),
% 51.94/6.98      inference(renaming,[status(thm)],[c_3224]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4006,plain,
% 51.94/6.98      ( m1_pre_topc(sK2,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_4001,c_3225]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1462,plain,
% 51.94/6.98      ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,X1_52,sK4),u1_struct_0(X1_52),u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(X1_52,X0_52)
% 51.94/6.98      | ~ m1_pre_topc(sK0,X0_52)
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(X0_52)
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | ~ l1_pre_topc(X0_52)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_282]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_15676,plain,
% 51.94/6.98      ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(sK3,X0_52)
% 51.94/6.98      | ~ m1_pre_topc(sK0,X0_52)
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(X0_52)
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | ~ l1_pre_topc(X0_52)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1462]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_15681,plain,
% 51.94/6.98      ( v1_funct_2(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 51.94/6.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,X0_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X0_52) != iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_15676]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_15683,plain,
% 51.94/6.98      ( v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 51.94/6.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_15681]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1447,plain,
% 51.94/6.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X1_52)
% 51.94/6.98      | ~ m1_pre_topc(sK0,X1_52)
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | v1_funct_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,sK4))
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_281]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_24600,plain,
% 51.94/6.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(sK3,X0_52)
% 51.94/6.98      | ~ m1_pre_topc(sK0,X0_52)
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(X0_52)
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | ~ l1_pre_topc(X0_52)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | v1_funct_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4))
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1447]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_24601,plain,
% 51.94/6.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,X0_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X0_52) != iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v1_funct_1(k3_tmap_1(X0_52,sK1,sK0,sK3,sK4)) = iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_24600]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_24603,plain,
% 51.94/6.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_24601]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2410,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(X0_52,X1_52)
% 51.94/6.98      | ~ m1_pre_topc(sK0,X1_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | m1_subset_1(k3_tmap_1(X1_52,sK1,sK0,X0_52,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_52),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(X1_52)
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | v2_struct_0(X1_52)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | ~ l1_pre_topc(X1_52)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ v1_funct_1(X0_53) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_283]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_28103,plain,
% 51.94/6.98      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(sK3,X0_52)
% 51.94/6.98      | ~ m1_pre_topc(sK0,X0_52)
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | m1_subset_1(k3_tmap_1(X0_52,sK1,sK0,sK3,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(X0_52)
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | v2_struct_0(X0_52)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | ~ l1_pre_topc(X0_52)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ v1_funct_1(X0_53) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_2410]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_28106,plain,
% 51.94/6.98      ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,X0_52) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,X0_52) != iProver_top
% 51.94/6.98      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | m1_subset_1(k3_tmap_1(X0_52,sK1,sK0,sK3,X0_53),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 51.94/6.98      | v2_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_struct_0(X0_52) = iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | l1_pre_topc(X0_52) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v1_funct_1(X0_53) != iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_28103]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_28108,plain,
% 51.94/6.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_28106]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_55842,plain,
% 51.94/6.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_5476,c_31,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,
% 51.94/6.98                 c_40,c_41,c_42,c_43,c_341,c_275,c_1517,c_1631,c_1916,
% 51.94/6.98                 c_4004,c_4005,c_4006,c_15683,c_24603,c_28108]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_274,negated_conjecture,
% 51.94/6.98      ( m1_pre_topc(sK3,sK0) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_21]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_900,plain,
% 51.94/6.98      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 51.94/6.98      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3250,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_900,c_3238]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2358,plain,
% 51.94/6.98      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_900,c_2351]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3304,plain,
% 51.94/6.98      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 51.94/6.98      inference(light_normalisation,[status(thm)],[c_3250,c_2358]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_21051,plain,
% 51.94/6.98      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_3304,c_31,c_32,c_33,c_37,c_38,c_39,c_40,c_341,c_275,
% 51.94/6.98                 c_1517,c_1631,c_1916]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_55846,plain,
% 51.94/6.98      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 51.94/6.98      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
% 51.94/6.98      inference(light_normalisation,[status(thm)],[c_55842,c_21051]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_16,negated_conjecture,
% 51.94/6.98      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
% 51.94/6.98      inference(cnf_transformation,[],[f72]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_311,plain,
% 51.94/6.98      ( u1_struct_0(X0_52) = u1_struct_0(X1_52) | X0_52 != X1_52 ),
% 51.94/6.98      theory(equality) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_329,plain,
% 51.94/6.98      ( u1_struct_0(sK0) = u1_struct_0(sK0) | sK0 != sK0 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_311]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_298,plain,( X0_53 = X0_53 ),theory(equality) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_342,plain,
% 51.94/6.98      ( sK4 = sK4 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_298]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2,plain,
% 51.94/6.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f44]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_293,plain,
% 51.94/6.98      ( ~ l1_pre_topc(X0_52) | l1_struct_0(X0_52) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_2]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_270,negated_conjecture,
% 51.94/6.98      ( l1_pre_topc(sK1) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_25]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1536,plain,
% 51.94/6.98      ( l1_struct_0(sK1) ),
% 51.94/6.98      inference(resolution,[status(thm)],[c_293,c_270]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4,plain,
% 51.94/6.98      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 51.94/6.98      | ~ v1_funct_2(X5,X2,X3)
% 51.94/6.98      | ~ v1_funct_2(X4,X0,X1)
% 51.94/6.98      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 51.94/6.98      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.94/6.98      | v1_xboole_0(X1)
% 51.94/6.98      | v1_xboole_0(X3)
% 51.94/6.98      | ~ v1_funct_1(X5)
% 51.94/6.98      | ~ v1_funct_1(X4) ),
% 51.94/6.98      inference(cnf_transformation,[],[f46]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_291,plain,
% 51.94/6.98      ( r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X0_53)
% 51.94/6.98      | ~ v1_funct_2(X1_53,X2_54,X3_54)
% 51.94/6.98      | ~ v1_funct_2(X0_53,X0_54,X1_54)
% 51.94/6.98      | ~ m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54)))
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 51.94/6.98      | v1_xboole_0(X1_54)
% 51.94/6.98      | v1_xboole_0(X3_54)
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | ~ v1_funct_1(X1_53) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_4]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1452,plain,
% 51.94/6.98      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_54,X1_54,sK4,sK4)
% 51.94/6.98      | ~ v1_funct_2(X0_53,X0_54,X1_54)
% 51.94/6.98      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | v1_xboole_0(X1_54)
% 51.94/6.98      | v1_xboole_0(u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_1(X0_53)
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_291]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1573,plain,
% 51.94/6.98      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.94/6.98      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | v1_xboole_0(u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1452]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_299,plain,( X0_54 = X0_54 ),theory(equality) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1875,plain,
% 51.94/6.98      ( u1_struct_0(sK1) = u1_struct_0(sK1) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_299]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_3,plain,
% 51.94/6.98      ( v2_struct_0(X0)
% 51.94/6.98      | ~ v1_xboole_0(u1_struct_0(X0))
% 51.94/6.98      | ~ l1_struct_0(X0) ),
% 51.94/6.98      inference(cnf_transformation,[],[f45]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_292,plain,
% 51.94/6.98      ( v2_struct_0(X0_52)
% 51.94/6.98      | ~ v1_xboole_0(u1_struct_0(X0_52))
% 51.94/6.98      | ~ l1_struct_0(X0_52) ),
% 51.94/6.98      inference(subtyping,[status(esa)],[c_3]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2651,plain,
% 51.94/6.98      ( v2_struct_0(sK1)
% 51.94/6.98      | ~ v1_xboole_0(u1_struct_0(sK1))
% 51.94/6.98      | ~ l1_struct_0(sK1) ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_292]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1570,plain,
% 51.94/6.98      ( u1_struct_0(X0_52) = u1_struct_0(sK0) | X0_52 != sK0 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_311]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_5906,plain,
% 51.94/6.98      ( u1_struct_0(k1_tsep_1(X0_52,X1_52,X2_52)) = u1_struct_0(sK0)
% 51.94/6.98      | k1_tsep_1(X0_52,X1_52,X2_52) != sK0 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1570]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_7105,plain,
% 51.94/6.98      ( u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) = u1_struct_0(sK0)
% 51.94/6.98      | k1_tsep_1(sK0,sK2,sK3) != sK0 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_5906]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_314,plain,
% 51.94/6.98      ( ~ r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X1_53)
% 51.94/6.98      | r1_funct_2(X4_54,X5_54,X6_54,X7_54,X2_53,X3_53)
% 51.94/6.98      | X4_54 != X0_54
% 51.94/6.98      | X5_54 != X1_54
% 51.94/6.98      | X6_54 != X2_54
% 51.94/6.98      | X7_54 != X3_54
% 51.94/6.98      | X2_53 != X0_53
% 51.94/6.98      | X3_53 != X1_53 ),
% 51.94/6.98      theory(equality) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1660,plain,
% 51.94/6.98      ( r1_funct_2(X0_54,X1_54,X2_54,X3_54,X0_53,X1_53)
% 51.94/6.98      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.94/6.98      | X1_54 != u1_struct_0(sK1)
% 51.94/6.98      | X3_54 != u1_struct_0(sK1)
% 51.94/6.98      | X0_54 != u1_struct_0(sK0)
% 51.94/6.98      | X2_54 != u1_struct_0(sK0)
% 51.94/6.98      | X0_53 != sK4
% 51.94/6.98      | X1_53 != sK4 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_314]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_2326,plain,
% 51.94/6.98      ( r1_funct_2(X0_54,X1_54,X2_54,u1_struct_0(sK1),X0_53,X1_53)
% 51.94/6.98      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.94/6.98      | X1_54 != u1_struct_0(sK1)
% 51.94/6.98      | X0_54 != u1_struct_0(sK0)
% 51.94/6.98      | X2_54 != u1_struct_0(sK0)
% 51.94/6.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.94/6.98      | X0_53 != sK4
% 51.94/6.98      | X1_53 != sK4 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1660]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4163,plain,
% 51.94/6.98      ( r1_funct_2(X0_54,u1_struct_0(sK1),X1_54,u1_struct_0(sK1),X0_53,X1_53)
% 51.94/6.98      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.94/6.98      | X0_54 != u1_struct_0(sK0)
% 51.94/6.98      | X1_54 != u1_struct_0(sK0)
% 51.94/6.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.94/6.98      | X0_53 != sK4
% 51.94/6.98      | X1_53 != sK4 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_2326]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_8512,plain,
% 51.94/6.98      ( r1_funct_2(X0_54,u1_struct_0(sK1),u1_struct_0(X0_52),u1_struct_0(sK1),X0_53,X1_53)
% 51.94/6.98      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.94/6.98      | X0_54 != u1_struct_0(sK0)
% 51.94/6.98      | u1_struct_0(X0_52) != u1_struct_0(sK0)
% 51.94/6.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.94/6.98      | X0_53 != sK4
% 51.94/6.98      | X1_53 != sK4 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_4163]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_10859,plain,
% 51.94/6.98      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(X0_52),u1_struct_0(sK1),X0_53,X1_53)
% 51.94/6.98      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.94/6.98      | u1_struct_0(X0_52) != u1_struct_0(sK0)
% 51.94/6.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.94/6.98      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 51.94/6.98      | X0_53 != sK4
% 51.94/6.98      | X1_53 != sK4 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_8512]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_14724,plain,
% 51.94/6.98      ( r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 51.94/6.98      | ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK1),sK4,sK4)
% 51.94/6.98      | u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) != u1_struct_0(sK0)
% 51.94/6.98      | u1_struct_0(sK1) != u1_struct_0(sK1)
% 51.94/6.98      | u1_struct_0(sK0) != u1_struct_0(sK0)
% 51.94/6.98      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 51.94/6.98      | sK4 != sK4 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_10859]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_55851,plain,
% 51.94/6.98      ( v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top ),
% 51.94/6.98      inference(global_propositional_subsumption,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_55846,c_27,c_19,c_18,c_17,c_16,c_329,c_341,c_342,
% 51.94/6.98                 c_275,c_1536,c_1573,c_1875,c_2651,c_7105,c_14724]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_55855,plain,
% 51.94/6.98      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 51.94/6.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 51.94/6.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_5296,c_55851]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_55856,plain,
% 51.94/6.98      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 51.94/6.98      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 51.94/6.98      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 51.94/6.98      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 51.94/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_55855]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_21059,plain,
% 51.94/6.98      ( m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_21051,c_3225]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_21270,plain,
% 51.94/6.98      ( ~ m1_pre_topc(sK3,sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK0,sK0)
% 51.94/6.98      | ~ v2_pre_topc(sK0)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK0)
% 51.94/6.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 51.94/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_21059]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_21057,plain,
% 51.94/6.98      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 51.94/6.98      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_21051,c_893]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_21269,plain,
% 51.94/6.98      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(sK3,sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK0,sK0)
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | ~ v2_pre_topc(sK0)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ l1_pre_topc(sK0)
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_21057]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_21056,plain,
% 51.94/6.98      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK3,sK0) != iProver_top
% 51.94/6.98      | m1_pre_topc(sK0,sK0) != iProver_top
% 51.94/6.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) = iProver_top
% 51.94/6.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK1) != iProver_top
% 51.94/6.98      | v2_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v2_struct_0(sK1) = iProver_top
% 51.94/6.98      | v2_struct_0(sK0) = iProver_top
% 51.94/6.98      | l1_pre_topc(sK1) != iProver_top
% 51.94/6.98      | l1_pre_topc(sK0) != iProver_top
% 51.94/6.98      | v1_funct_1(sK4) != iProver_top ),
% 51.94/6.98      inference(superposition,[status(thm)],[c_21051,c_892]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_21268,plain,
% 51.94/6.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(sK3,sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK0,sK0)
% 51.94/6.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | ~ v2_pre_topc(sK0)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ l1_pre_topc(sK0)
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_21056]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4069,plain,
% 51.94/6.98      ( ~ m1_pre_topc(sK2,sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK0,sK0)
% 51.94/6.98      | ~ v2_pre_topc(sK0)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK0)
% 51.94/6.98      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 51.94/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_4006]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4068,plain,
% 51.94/6.98      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 51.94/6.98      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(sK2,sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK0,sK0)
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | ~ v2_pre_topc(sK0)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ l1_pre_topc(sK0)
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_4005]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_4067,plain,
% 51.94/6.98      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 51.94/6.98      | ~ m1_pre_topc(sK2,sK0)
% 51.94/6.98      | ~ m1_pre_topc(sK0,sK0)
% 51.94/6.98      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 51.94/6.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 51.94/6.98      | ~ v2_pre_topc(sK1)
% 51.94/6.98      | ~ v2_pre_topc(sK0)
% 51.94/6.98      | v2_struct_0(sK1)
% 51.94/6.98      | v2_struct_0(sK0)
% 51.94/6.98      | ~ l1_pre_topc(sK1)
% 51.94/6.98      | ~ l1_pre_topc(sK0)
% 51.94/6.98      | ~ v1_funct_1(sK4) ),
% 51.94/6.98      inference(predicate_to_equality_rev,[status(thm)],[c_4004]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(c_1630,plain,
% 51.94/6.98      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK3),sK0)
% 51.94/6.98      | m1_pre_topc(sK0,sK0)
% 51.94/6.98      | sK0 != k1_tsep_1(sK0,sK2,sK3)
% 51.94/6.98      | sK0 != sK0 ),
% 51.94/6.98      inference(instantiation,[status(thm)],[c_1628]) ).
% 51.94/6.98  
% 51.94/6.98  cnf(contradiction,plain,
% 51.94/6.98      ( $false ),
% 51.94/6.98      inference(minisat,
% 51.94/6.98                [status(thm)],
% 51.94/6.98                [c_138545,c_55856,c_21270,c_21269,c_21268,c_4069,c_4068,
% 51.94/6.98                 c_4067,c_1916,c_1630,c_1516,c_275,c_341,c_17,c_18,c_19,
% 51.94/6.98                 c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29,c_30]) ).
% 51.94/6.98  
% 51.94/6.98  
% 51.94/6.98  % SZS output end CNFRefutation for theBenchmark.p
% 51.94/6.98  
% 51.94/6.98  ------                               Statistics
% 51.94/6.98  
% 51.94/6.98  ------ Selected
% 51.94/6.98  
% 51.94/6.98  total_time:                             6.5
% 51.94/6.98  
%------------------------------------------------------------------------------
