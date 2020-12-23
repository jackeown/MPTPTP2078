%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:47 EST 2020

% Result     : Theorem 3.29s
% Output     : Refutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :  225 (3720 expanded)
%              Number of leaves         :   28 (1786 expanded)
%              Depth                    :   33
%              Number of atoms          : 1439 (52341 expanded)
%              Number of equality atoms :   69 (4002 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3478,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f248,f255,f264,f271,f292,f297,f324,f361,f1390,f3442,f3477])).

fof(f3477,plain,(
    ~ spl7_57 ),
    inference(avatar_contradiction_clause,[],[f3476])).

fof(f3476,plain,
    ( $false
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f3475,f54])).

fof(f54,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & sK2 = k1_tsep_1(sK2,sK4,sK5)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f43,f42,f41,f40,f39])).

fof(f39,plain,
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
                      ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & sK2 = k1_tsep_1(sK2,X2,X3)
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

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3)))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & sK2 = k1_tsep_1(sK2,X2,X3)
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3)))
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & sK2 = k1_tsep_1(sK2,X2,X3)
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3)))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & sK2 = k1_tsep_1(sK2,X2,X3)
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3)))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & sK2 = k1_tsep_1(sK2,sK4,X3)
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3)))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & sK2 = k1_tsep_1(sK2,sK4,X3)
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5)))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & sK2 = k1_tsep_1(sK2,sK4,sK5)
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X4] :
        ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).

fof(f3475,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f3474,f91])).

fof(f91,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f66,f56])).

fof(f56,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f3474,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_57 ),
    inference(resolution,[],[f3473,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f3473,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f3472,f62])).

fof(f62,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f3472,plain,
    ( ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f3471,f63])).

fof(f63,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f3471,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f3470,f64])).

fof(f64,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f3470,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_57 ),
    inference(duplicate_literal_removal,[],[f3469])).

fof(f3469,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_57 ),
    inference(resolution,[],[f3468,f87])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(f3468,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK6)
    | ~ spl7_57 ),
    inference(backward_demodulation,[],[f89,f1389])).

fof(f1389,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f1387])).

fof(f1387,plain,
    ( spl7_57
  <=> sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f89,plain,(
    ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) ),
    inference(backward_demodulation,[],[f65,f61])).

fof(f61,plain,(
    sK2 = k1_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) ),
    inference(cnf_transformation,[],[f44])).

fof(f3442,plain,
    ( ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(avatar_contradiction_clause,[],[f3441])).

fof(f3441,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3440,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f3440,plain,
    ( v2_struct_0(sK2)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3439,f52])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f3439,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3438,f53])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f3438,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3437,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f3437,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3436,f58])).

fof(f58,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f3436,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3435,f60])).

fof(f60,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f3435,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3434,f247])).

fof(f247,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl7_2
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f3434,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3433,f291])).

fof(f291,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl7_7
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f3433,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(subsumption_resolution,[],[f3428,f323])).

fof(f323,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl7_10
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f3428,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_11
    | spl7_56 ),
    inference(resolution,[],[f373,f1385])).

fof(f1385,plain,
    ( ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))
    | spl7_56 ),
    inference(avatar_component_clause,[],[f1383])).

fof(f1383,plain,
    ( spl7_56
  <=> sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f373,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f372,f54])).

fof(f372,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f371,f55])).

fof(f55,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f371,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f370,f56])).

fof(f370,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f369,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f369,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f368,f263])).

fof(f263,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl7_4
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f368,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f362,f296])).

fof(f296,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl7_8
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f362,plain,
    ( ! [X2,X0,X1] :
        ( sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(X2)
        | ~ m1_pre_topc(sK5,X1)
        | v2_struct_0(sK5)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl7_11 ),
    inference(resolution,[],[f360,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | sP1(X1,X3,X2,X0,X5,X4)
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP1(X1,X3,X2,X0,X5,X4)
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
    inference(definition_folding,[],[f34,f37])).

fof(f37,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP1(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

fof(f360,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl7_11
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1390,plain,
    ( ~ spl7_56
    | spl7_57 ),
    inference(avatar_split_clause,[],[f784,f1387,f1383])).

fof(f784,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f783,f62])).

fof(f783,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f782,f63])).

fof(f782,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f781,f64])).

fof(f781,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    inference(resolution,[],[f739,f126])).

fof(f126,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14))))
      | ~ v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14))
      | ~ v1_funct_1(X15)
      | ~ sP1(X14,sK5,sK4,sK2,X17,X16) ) ),
    inference(subsumption_resolution,[],[f125,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
        & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
        & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP1(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f125,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15
      | ~ v1_funct_1(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14))))
      | ~ v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14))
      | ~ v1_funct_1(X15)
      | ~ sP1(X14,sK5,sK4,sK2,X17,X16) ) ),
    inference(subsumption_resolution,[],[f118,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ sP1(X0,sK5,sK4,sK2,X2,X1) ) ),
    inference(superposition,[],[f82,f61])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,(
    ! [X14,X17,X15,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15
      | ~ v1_funct_2(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17),u1_struct_0(sK2),u1_struct_0(X14))
      | ~ v1_funct_1(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14))))
      | ~ v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14))
      | ~ v1_funct_1(X15)
      | ~ sP1(X14,sK5,sK4,sK2,X17,X16) ) ),
    inference(resolution,[],[f73,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ sP1(X0,sK5,sK4,sK2,X2,X1) ) ),
    inference(superposition,[],[f83,f61])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0))))
      | ~ sP1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f739,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) ),
    inference(forward_demodulation,[],[f738,f208])).

fof(f208,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6) ),
    inference(forward_demodulation,[],[f204,f178])).

fof(f178,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5)) ),
    inference(resolution,[],[f167,f60])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f166,f51])).

fof(f166,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f165,f52])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f164,f53])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f163,f54])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f162,f55])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f161,f56])).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f160,f62])).

fof(f160,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f156,f63])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f70,f64])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f204,plain,(
    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6) ),
    inference(resolution,[],[f202,f60])).

fof(f202,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) ) ),
    inference(subsumption_resolution,[],[f201,f51])).

fof(f201,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f200,f52])).

fof(f200,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f199,f53])).

fof(f199,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f191,f105])).

fof(f105,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f104,f51])).

fof(f104,plain,
    ( m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f103,f53])).

fof(f103,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,
    ( m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f101,f58])).

fof(f101,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f100,f59])).

fof(f100,plain,
    ( m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f99,f60])).

fof(f99,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f72,f61])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f190,f54])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f189,f55])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f188,f56])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f187,f62])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f183,f63])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f68,f64])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
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
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f738,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) ),
    inference(subsumption_resolution,[],[f737,f54])).

fof(f737,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f736,f55])).

fof(f736,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f735,f56])).

fof(f735,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f734,f62])).

fof(f734,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f733,f63])).

fof(f733,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f730,f64])).

fof(f730,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f482,f207])).

fof(f207,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6) ),
    inference(forward_demodulation,[],[f203,f177])).

fof(f177,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) ),
    inference(resolution,[],[f167,f58])).

fof(f203,plain,(
    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6) ),
    inference(resolution,[],[f202,f58])).

fof(f482,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f481,f51])).

fof(f481,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f480,f52])).

fof(f480,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f479,f53])).

fof(f479,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f478,f57])).

fof(f478,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f477,f58])).

fof(f477,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f476,f59])).

fof(f476,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f475,f60])).

fof(f475,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ m1_pre_topc(sK5,sK2)
      | v2_struct_0(sK5)
      | ~ m1_pre_topc(sK4,sK2)
      | v2_struct_0(sK4)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(superposition,[],[f69,f61])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).

fof(f361,plain,
    ( ~ spl7_3
    | spl7_11 ),
    inference(avatar_split_clause,[],[f224,f358,f257])).

fof(f257,plain,
    ( spl7_3
  <=> sP0(sK3,sK5,sK6,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f224,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ sP0(sK3,sK5,sK6,sK2,sK2) ),
    inference(superposition,[],[f77,f208])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP0(X1,X3,X4,X2,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X3,X4,X2,X0] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
      | ~ sP0(X1,X3,X4,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f324,plain,
    ( ~ spl7_1
    | spl7_10 ),
    inference(avatar_split_clause,[],[f215,f321,f241])).

fof(f241,plain,
    ( spl7_1
  <=> sP0(sK3,sK4,sK6,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f215,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ sP0(sK3,sK4,sK6,sK2,sK2) ),
    inference(superposition,[],[f77,f207])).

fof(f297,plain,
    ( ~ spl7_3
    | spl7_8 ),
    inference(avatar_split_clause,[],[f225,f294,f257])).

fof(f225,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ sP0(sK3,sK5,sK6,sK2,sK2) ),
    inference(superposition,[],[f76,f208])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f292,plain,
    ( ~ spl7_1
    | spl7_7 ),
    inference(avatar_split_clause,[],[f216,f289,f241])).

fof(f216,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ sP0(sK3,sK4,sK6,sK2,sK2) ),
    inference(superposition,[],[f76,f207])).

fof(f271,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f269,f51])).

fof(f269,plain,
    ( v2_struct_0(sK2)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f268,f52])).

fof(f268,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f267,f53])).

fof(f267,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f266,f105])).

fof(f266,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f265,f60])).

fof(f265,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_3 ),
    inference(resolution,[],[f259,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f143,f54])).

fof(f143,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f142,f55])).

fof(f142,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f141,f56])).

fof(f141,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f140,f62])).

fof(f140,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f136,f63])).

fof(f136,plain,(
    ! [X0,X1] :
      ( sP0(sK3,X0,sK6,sK2,X1)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f78,f64])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | sP0(X1,X3,X4,X2,X0)
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( sP0(X1,X3,X4,X2,X0)
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
    inference(definition_folding,[],[f30,f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f259,plain,
    ( ~ sP0(sK3,sK5,sK6,sK2,sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f257])).

fof(f264,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f226,f261,f257])).

fof(f226,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ sP0(sK3,sK5,sK6,sK2,sK2) ),
    inference(superposition,[],[f75,f208])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f255,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f253,f51])).

fof(f253,plain,
    ( v2_struct_0(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f252,f52])).

fof(f252,plain,
    ( ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f251,f53])).

fof(f251,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f250,f105])).

fof(f250,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f249,f58])).

fof(f249,plain,
    ( ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | spl7_1 ),
    inference(resolution,[],[f243,f144])).

fof(f243,plain,
    ( ~ sP0(sK3,sK4,sK6,sK2,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f241])).

fof(f248,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f217,f245,f241])).

fof(f217,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ sP0(sK3,sK4,sK6,sK2,sK2) ),
    inference(superposition,[],[f75,f207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (1275)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (1286)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (1285)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (1269)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (1284)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.50  % (1288)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (1268)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (1266)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (1280)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (1265)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (1279)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (1278)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (1265)Refutation not found, incomplete strategy% (1265)------------------------------
% 0.20/0.51  % (1265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (1287)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (1272)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (1276)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (1290)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (1271)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (1265)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (1265)Memory used [KB]: 10746
% 0.20/0.51  % (1265)Time elapsed: 0.092 s
% 0.20/0.51  % (1277)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (1265)------------------------------
% 0.20/0.51  % (1265)------------------------------
% 0.20/0.52  % (1267)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (1283)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.39/0.53  % (1281)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.39/0.53  % (1289)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.39/0.53  % (1270)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.39/0.53  % (1273)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.39/0.54  % (1270)Refutation not found, incomplete strategy% (1270)------------------------------
% 1.39/0.54  % (1270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (1270)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (1270)Memory used [KB]: 6268
% 1.39/0.54  % (1270)Time elapsed: 0.128 s
% 1.39/0.54  % (1270)------------------------------
% 1.39/0.54  % (1270)------------------------------
% 1.39/0.54  % (1271)Refutation not found, incomplete strategy% (1271)------------------------------
% 1.39/0.54  % (1271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (1271)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (1271)Memory used [KB]: 10874
% 1.39/0.54  % (1271)Time elapsed: 0.139 s
% 1.39/0.54  % (1271)------------------------------
% 1.39/0.54  % (1271)------------------------------
% 1.39/0.54  % (1282)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.39/0.54  % (1274)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.18/0.66  % (1274)Refutation not found, incomplete strategy% (1274)------------------------------
% 2.18/0.66  % (1274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.68  % (1274)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.68  
% 2.55/0.68  % (1274)Memory used [KB]: 6396
% 2.55/0.68  % (1274)Time elapsed: 0.268 s
% 2.55/0.68  % (1274)------------------------------
% 2.55/0.68  % (1274)------------------------------
% 3.29/0.81  % (1290)Refutation found. Thanks to Tanya!
% 3.29/0.81  % SZS status Theorem for theBenchmark
% 3.67/0.82  % SZS output start Proof for theBenchmark
% 3.67/0.82  fof(f3478,plain,(
% 3.67/0.82    $false),
% 3.67/0.82    inference(avatar_sat_refutation,[],[f248,f255,f264,f271,f292,f297,f324,f361,f1390,f3442,f3477])).
% 3.67/0.82  fof(f3477,plain,(
% 3.67/0.82    ~spl7_57),
% 3.67/0.82    inference(avatar_contradiction_clause,[],[f3476])).
% 3.67/0.82  fof(f3476,plain,(
% 3.67/0.82    $false | ~spl7_57),
% 3.67/0.82    inference(subsumption_resolution,[],[f3475,f54])).
% 3.67/0.82  fof(f54,plain,(
% 3.67/0.82    ~v2_struct_0(sK3)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f44,plain,(
% 3.67/0.82    ((((~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & sK2 = k1_tsep_1(sK2,sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.67/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f43,f42,f41,f40,f39])).
% 3.67/0.82  fof(f39,plain,(
% 3.67/0.82    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.67/0.82    introduced(choice_axiom,[])).
% 3.67/0.82  fof(f40,plain,(
% 3.67/0.82    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 3.67/0.82    introduced(choice_axiom,[])).
% 3.67/0.82  fof(f41,plain,(
% 3.67/0.82    ? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 3.67/0.82    introduced(choice_axiom,[])).
% 3.67/0.82  fof(f42,plain,(
% 3.67/0.82    ? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 3.67/0.82    introduced(choice_axiom,[])).
% 3.67/0.82  fof(f43,plain,(
% 3.67/0.82    ? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 3.67/0.82    introduced(choice_axiom,[])).
% 3.67/0.82  fof(f15,plain,(
% 3.67/0.82    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.67/0.82    inference(flattening,[],[f14])).
% 3.67/0.82  fof(f14,plain,(
% 3.67/0.82    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.67/0.82    inference(ennf_transformation,[],[f12])).
% 3.67/0.82  fof(f12,negated_conjecture,(
% 3.67/0.82    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 3.67/0.82    inference(negated_conjecture,[],[f11])).
% 3.67/0.82  fof(f11,conjecture,(
% 3.67/0.82    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).
% 3.67/0.82  fof(f3475,plain,(
% 3.67/0.82    v2_struct_0(sK3) | ~spl7_57),
% 3.67/0.82    inference(subsumption_resolution,[],[f3474,f91])).
% 3.67/0.82  fof(f91,plain,(
% 3.67/0.82    l1_struct_0(sK3)),
% 3.67/0.82    inference(resolution,[],[f66,f56])).
% 3.67/0.82  fof(f56,plain,(
% 3.67/0.82    l1_pre_topc(sK3)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f66,plain,(
% 3.67/0.82    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f16])).
% 3.67/0.82  fof(f16,plain,(
% 3.67/0.82    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.67/0.82    inference(ennf_transformation,[],[f2])).
% 3.67/0.82  fof(f2,axiom,(
% 3.67/0.82    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 3.67/0.82  fof(f3474,plain,(
% 3.67/0.82    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl7_57),
% 3.67/0.82    inference(resolution,[],[f3473,f67])).
% 3.67/0.82  fof(f67,plain,(
% 3.67/0.82    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f18])).
% 3.67/0.82  fof(f18,plain,(
% 3.67/0.82    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(flattening,[],[f17])).
% 3.67/0.82  fof(f17,plain,(
% 3.67/0.82    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.67/0.82    inference(ennf_transformation,[],[f3])).
% 3.67/0.82  fof(f3,axiom,(
% 3.67/0.82    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 3.67/0.82  fof(f3473,plain,(
% 3.67/0.82    v1_xboole_0(u1_struct_0(sK3)) | ~spl7_57),
% 3.67/0.82    inference(subsumption_resolution,[],[f3472,f62])).
% 3.67/0.82  fof(f62,plain,(
% 3.67/0.82    v1_funct_1(sK6)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3472,plain,(
% 3.67/0.82    ~v1_funct_1(sK6) | v1_xboole_0(u1_struct_0(sK3)) | ~spl7_57),
% 3.67/0.82    inference(subsumption_resolution,[],[f3471,f63])).
% 3.67/0.82  fof(f63,plain,(
% 3.67/0.82    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3471,plain,(
% 3.67/0.82    ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v1_xboole_0(u1_struct_0(sK3)) | ~spl7_57),
% 3.67/0.82    inference(subsumption_resolution,[],[f3470,f64])).
% 3.67/0.82  fof(f64,plain,(
% 3.67/0.82    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3470,plain,(
% 3.67/0.82    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v1_xboole_0(u1_struct_0(sK3)) | ~spl7_57),
% 3.67/0.82    inference(duplicate_literal_removal,[],[f3469])).
% 3.67/0.82  fof(f3469,plain,(
% 3.67/0.82    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | ~spl7_57),
% 3.67/0.82    inference(resolution,[],[f3468,f87])).
% 3.67/0.82  fof(f87,plain,(
% 3.67/0.82    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.67/0.82    inference(duplicate_literal_removal,[],[f86])).
% 3.67/0.82  fof(f86,plain,(
% 3.67/0.82    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.67/0.82    inference(equality_resolution,[],[f80])).
% 3.67/0.82  fof(f80,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f48])).
% 3.67/0.82  fof(f48,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.67/0.82    inference(nnf_transformation,[],[f32])).
% 3.67/0.82  fof(f32,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.67/0.82    inference(flattening,[],[f31])).
% 3.67/0.82  fof(f31,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.67/0.82    inference(ennf_transformation,[],[f4])).
% 3.67/0.82  fof(f4,axiom,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 3.67/0.82  fof(f3468,plain,(
% 3.67/0.82    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK6) | ~spl7_57),
% 3.67/0.82    inference(backward_demodulation,[],[f89,f1389])).
% 3.67/0.82  fof(f1389,plain,(
% 3.67/0.82    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~spl7_57),
% 3.67/0.82    inference(avatar_component_clause,[],[f1387])).
% 3.67/0.82  fof(f1387,plain,(
% 3.67/0.82    spl7_57 <=> sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 3.67/0.82  fof(f89,plain,(
% 3.67/0.82    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))),
% 3.67/0.82    inference(backward_demodulation,[],[f65,f61])).
% 3.67/0.82  fof(f61,plain,(
% 3.67/0.82    sK2 = k1_tsep_1(sK2,sK4,sK5)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f65,plain,(
% 3.67/0.82    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3442,plain,(
% 3.67/0.82    ~spl7_2 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56),
% 3.67/0.82    inference(avatar_contradiction_clause,[],[f3441])).
% 3.67/0.82  fof(f3441,plain,(
% 3.67/0.82    $false | (~spl7_2 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3440,f51])).
% 3.67/0.82  fof(f51,plain,(
% 3.67/0.82    ~v2_struct_0(sK2)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3440,plain,(
% 3.67/0.82    v2_struct_0(sK2) | (~spl7_2 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3439,f52])).
% 3.67/0.82  fof(f52,plain,(
% 3.67/0.82    v2_pre_topc(sK2)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3439,plain,(
% 3.67/0.82    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_2 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3438,f53])).
% 3.67/0.82  fof(f53,plain,(
% 3.67/0.82    l1_pre_topc(sK2)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3438,plain,(
% 3.67/0.82    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_2 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3437,f57])).
% 3.67/0.82  fof(f57,plain,(
% 3.67/0.82    ~v2_struct_0(sK4)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3437,plain,(
% 3.67/0.82    v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_2 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3436,f58])).
% 3.67/0.82  fof(f58,plain,(
% 3.67/0.82    m1_pre_topc(sK4,sK2)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3436,plain,(
% 3.67/0.82    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_2 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3435,f60])).
% 3.67/0.82  fof(f60,plain,(
% 3.67/0.82    m1_pre_topc(sK5,sK2)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f3435,plain,(
% 3.67/0.82    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_2 | ~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3434,f247])).
% 3.67/0.82  fof(f247,plain,(
% 3.67/0.82    v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~spl7_2),
% 3.67/0.82    inference(avatar_component_clause,[],[f245])).
% 3.67/0.82  fof(f245,plain,(
% 3.67/0.82    spl7_2 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 3.67/0.82  fof(f3434,plain,(
% 3.67/0.82    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3433,f291])).
% 3.67/0.82  fof(f291,plain,(
% 3.67/0.82    v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~spl7_7),
% 3.67/0.82    inference(avatar_component_clause,[],[f289])).
% 3.67/0.82  fof(f289,plain,(
% 3.67/0.82    spl7_7 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 3.67/0.82  fof(f3433,plain,(
% 3.67/0.82    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_4 | ~spl7_8 | ~spl7_10 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(subsumption_resolution,[],[f3428,f323])).
% 3.67/0.82  fof(f323,plain,(
% 3.67/0.82    m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~spl7_10),
% 3.67/0.82    inference(avatar_component_clause,[],[f321])).
% 3.67/0.82  fof(f321,plain,(
% 3.67/0.82    spl7_10 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 3.67/0.82  fof(f3428,plain,(
% 3.67/0.82    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_4 | ~spl7_8 | ~spl7_11 | spl7_56)),
% 3.67/0.82    inference(resolution,[],[f373,f1385])).
% 3.67/0.82  fof(f1385,plain,(
% 3.67/0.82    ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) | spl7_56),
% 3.67/0.82    inference(avatar_component_clause,[],[f1383])).
% 3.67/0.82  fof(f1383,plain,(
% 3.67/0.82    spl7_56 <=> sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 3.67/0.82  fof(f373,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_4 | ~spl7_8 | ~spl7_11)),
% 3.67/0.82    inference(subsumption_resolution,[],[f372,f54])).
% 3.67/0.82  fof(f372,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_4 | ~spl7_8 | ~spl7_11)),
% 3.67/0.82    inference(subsumption_resolution,[],[f371,f55])).
% 3.67/0.82  fof(f55,plain,(
% 3.67/0.82    v2_pre_topc(sK3)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f371,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_4 | ~spl7_8 | ~spl7_11)),
% 3.67/0.82    inference(subsumption_resolution,[],[f370,f56])).
% 3.67/0.82  fof(f370,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_4 | ~spl7_8 | ~spl7_11)),
% 3.67/0.82    inference(subsumption_resolution,[],[f369,f59])).
% 3.67/0.82  fof(f59,plain,(
% 3.67/0.82    ~v2_struct_0(sK5)),
% 3.67/0.82    inference(cnf_transformation,[],[f44])).
% 3.67/0.82  fof(f369,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | v2_struct_0(sK5) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_4 | ~spl7_8 | ~spl7_11)),
% 3.67/0.82    inference(subsumption_resolution,[],[f368,f263])).
% 3.67/0.82  fof(f263,plain,(
% 3.67/0.82    v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) | ~spl7_4),
% 3.67/0.82    inference(avatar_component_clause,[],[f261])).
% 3.67/0.82  fof(f261,plain,(
% 3.67/0.82    spl7_4 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5))),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 3.67/0.82  fof(f368,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | v2_struct_0(sK5) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | (~spl7_8 | ~spl7_11)),
% 3.67/0.82    inference(subsumption_resolution,[],[f362,f296])).
% 3.67/0.82  fof(f296,plain,(
% 3.67/0.82    v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl7_8),
% 3.67/0.82    inference(avatar_component_clause,[],[f294])).
% 3.67/0.82  fof(f294,plain,(
% 3.67/0.82    spl7_8 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3))),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 3.67/0.82  fof(f362,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (sP1(sK3,sK5,X0,X1,k2_tmap_1(sK2,sK3,sK6,sK5),X2) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(X2) | ~m1_pre_topc(sK5,X1) | v2_struct_0(sK5) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl7_11),
% 3.67/0.82    inference(resolution,[],[f360,f84])).
% 3.67/0.82  fof(f84,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP1(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f38])).
% 3.67/0.82  fof(f38,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : (sP1(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(definition_folding,[],[f34,f37])).
% 3.67/0.82  fof(f37,plain,(
% 3.67/0.82    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP1(X1,X3,X2,X0,X5,X4))),
% 3.67/0.82    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.67/0.82  fof(f34,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(flattening,[],[f33])).
% 3.67/0.82  fof(f33,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.82    inference(ennf_transformation,[],[f7])).
% 3.67/0.82  fof(f7,axiom,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 3.67/0.82  fof(f360,plain,(
% 3.67/0.82    m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl7_11),
% 3.67/0.82    inference(avatar_component_clause,[],[f358])).
% 3.67/0.82  fof(f358,plain,(
% 3.67/0.82    spl7_11 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 3.67/0.82  fof(f1390,plain,(
% 3.67/0.82    ~spl7_56 | spl7_57),
% 3.67/0.82    inference(avatar_split_clause,[],[f784,f1387,f1383])).
% 3.67/0.82  fof(f784,plain,(
% 3.67/0.82    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 3.67/0.82    inference(subsumption_resolution,[],[f783,f62])).
% 3.67/0.82  fof(f783,plain,(
% 3.67/0.82    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 3.67/0.82    inference(subsumption_resolution,[],[f782,f63])).
% 3.67/0.82  fof(f782,plain,(
% 3.67/0.82    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 3.67/0.82    inference(subsumption_resolution,[],[f781,f64])).
% 3.67/0.82  fof(f781,plain,(
% 3.67/0.82    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 3.67/0.82    inference(resolution,[],[f739,f126])).
% 3.67/0.82  fof(f126,plain,(
% 3.67/0.82    ( ! [X14,X17,X15,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15 | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14)))) | ~v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14)) | ~v1_funct_1(X15) | ~sP1(X14,sK5,sK4,sK2,X17,X16)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f125,f81])).
% 3.67/0.82  fof(f81,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f50])).
% 3.67/0.82  fof(f50,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP1(X0,X1,X2,X3,X4,X5))),
% 3.67/0.82    inference(rectify,[],[f49])).
% 3.67/0.82  fof(f49,plain,(
% 3.67/0.82    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP1(X1,X3,X2,X0,X5,X4))),
% 3.67/0.82    inference(nnf_transformation,[],[f37])).
% 3.67/0.82  fof(f125,plain,(
% 3.67/0.82    ( ! [X14,X17,X15,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15 | ~v1_funct_1(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14)))) | ~v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14)) | ~v1_funct_1(X15) | ~sP1(X14,sK5,sK4,sK2,X17,X16)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f118,f106])).
% 3.67/0.82  fof(f106,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),u1_struct_0(sK2),u1_struct_0(X0)) | ~sP1(X0,sK5,sK4,sK2,X2,X1)) )),
% 3.67/0.82    inference(superposition,[],[f82,f61])).
% 3.67/0.82  fof(f82,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f50])).
% 3.67/0.82  fof(f118,plain,(
% 3.67/0.82    ( ! [X14,X17,X15,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X14),X15,k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | k10_tmap_1(sK2,X14,sK4,sK5,X16,X17) = X15 | ~v1_funct_2(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17),u1_struct_0(sK2),u1_struct_0(X14)) | ~v1_funct_1(k10_tmap_1(sK2,X14,sK4,sK5,X16,X17)) | ~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X14)))) | ~v1_funct_2(X15,u1_struct_0(sK2),u1_struct_0(X14)) | ~v1_funct_1(X15) | ~sP1(X14,sK5,sK4,sK2,X17,X16)) )),
% 3.67/0.82    inference(resolution,[],[f73,f108])).
% 3.67/0.82  fof(f108,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~sP1(X0,sK5,sK4,sK2,X2,X1)) )),
% 3.67/0.82    inference(superposition,[],[f83,f61])).
% 3.67/0.82  fof(f83,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f50])).
% 3.67/0.82  fof(f73,plain,(
% 3.67/0.82    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f45])).
% 3.67/0.82  fof(f45,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.67/0.82    inference(nnf_transformation,[],[f28])).
% 3.67/0.82  fof(f28,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.67/0.82    inference(flattening,[],[f27])).
% 3.67/0.82  fof(f27,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.67/0.82    inference(ennf_transformation,[],[f1])).
% 3.67/0.82  fof(f1,axiom,(
% 3.67/0.82    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 3.67/0.82  fof(f739,plain,(
% 3.67/0.82    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))),
% 3.67/0.82    inference(forward_demodulation,[],[f738,f208])).
% 3.67/0.82  fof(f208,plain,(
% 3.67/0.82    k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6)),
% 3.67/0.82    inference(forward_demodulation,[],[f204,f178])).
% 3.67/0.82  fof(f178,plain,(
% 3.67/0.82    k2_tmap_1(sK2,sK3,sK6,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5))),
% 3.67/0.82    inference(resolution,[],[f167,f60])).
% 3.67/0.82  fof(f167,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f166,f51])).
% 3.67/0.82  fof(f166,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f165,f52])).
% 3.67/0.82  fof(f165,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f164,f53])).
% 3.67/0.82  fof(f164,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f163,f54])).
% 3.67/0.82  fof(f163,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f162,f55])).
% 3.67/0.82  fof(f162,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f161,f56])).
% 3.67/0.82  fof(f161,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f160,f62])).
% 3.67/0.82  fof(f160,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f156,f63])).
% 3.67/0.82  fof(f156,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(resolution,[],[f70,f64])).
% 3.67/0.82  fof(f70,plain,(
% 3.67/0.82    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f24])).
% 3.67/0.82  fof(f24,plain,(
% 3.67/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(flattening,[],[f23])).
% 3.67/0.82  fof(f23,plain,(
% 3.67/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.82    inference(ennf_transformation,[],[f5])).
% 3.67/0.82  fof(f5,axiom,(
% 3.67/0.82    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 3.67/0.82  fof(f204,plain,(
% 3.67/0.82    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6)),
% 3.67/0.82    inference(resolution,[],[f202,f60])).
% 3.67/0.82  fof(f202,plain,(
% 3.67/0.82    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f201,f51])).
% 3.67/0.82  fof(f201,plain,(
% 3.67/0.82    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f200,f52])).
% 3.67/0.82  fof(f200,plain,(
% 3.67/0.82    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f199,f53])).
% 3.67/0.82  fof(f199,plain,(
% 3.67/0.82    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(duplicate_literal_removal,[],[f198])).
% 3.67/0.82  fof(f198,plain,(
% 3.67/0.82    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(resolution,[],[f191,f105])).
% 3.67/0.82  fof(f105,plain,(
% 3.67/0.82    m1_pre_topc(sK2,sK2)),
% 3.67/0.82    inference(subsumption_resolution,[],[f104,f51])).
% 3.67/0.82  fof(f104,plain,(
% 3.67/0.82    m1_pre_topc(sK2,sK2) | v2_struct_0(sK2)),
% 3.67/0.82    inference(subsumption_resolution,[],[f103,f53])).
% 3.67/0.82  fof(f103,plain,(
% 3.67/0.82    m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 3.67/0.82    inference(subsumption_resolution,[],[f102,f57])).
% 3.67/0.82  fof(f102,plain,(
% 3.67/0.82    m1_pre_topc(sK2,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 3.67/0.82    inference(subsumption_resolution,[],[f101,f58])).
% 3.67/0.82  fof(f101,plain,(
% 3.67/0.82    m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 3.67/0.82    inference(subsumption_resolution,[],[f100,f59])).
% 3.67/0.82  fof(f100,plain,(
% 3.67/0.82    m1_pre_topc(sK2,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 3.67/0.82    inference(subsumption_resolution,[],[f99,f60])).
% 3.67/0.82  fof(f99,plain,(
% 3.67/0.82    m1_pre_topc(sK2,sK2) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 3.67/0.82    inference(superposition,[],[f72,f61])).
% 3.67/0.82  fof(f72,plain,(
% 3.67/0.82    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f26])).
% 3.67/0.82  fof(f26,plain,(
% 3.67/0.82    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(flattening,[],[f25])).
% 3.67/0.82  fof(f25,plain,(
% 3.67/0.82    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.82    inference(ennf_transformation,[],[f13])).
% 3.67/0.82  fof(f13,plain,(
% 3.67/0.82    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.67/0.82    inference(pure_predicate_removal,[],[f8])).
% 3.67/0.82  fof(f8,axiom,(
% 3.67/0.82    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 3.67/0.82  fof(f191,plain,(
% 3.67/0.82    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f190,f54])).
% 3.67/0.82  fof(f190,plain,(
% 3.67/0.82    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f189,f55])).
% 3.67/0.82  fof(f189,plain,(
% 3.67/0.82    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f188,f56])).
% 3.67/0.82  fof(f188,plain,(
% 3.67/0.82    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f187,f62])).
% 3.67/0.82  fof(f187,plain,(
% 3.67/0.82    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f183,f63])).
% 3.67/0.82  fof(f183,plain,(
% 3.67/0.82    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(resolution,[],[f68,f64])).
% 3.67/0.82  fof(f68,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f20])).
% 3.67/0.82  fof(f20,plain,(
% 3.67/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(flattening,[],[f19])).
% 3.67/0.82  fof(f19,plain,(
% 3.67/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.82    inference(ennf_transformation,[],[f6])).
% 3.67/0.82  fof(f6,axiom,(
% 3.67/0.82    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 3.67/0.82  fof(f738,plain,(
% 3.67/0.82    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))),
% 3.67/0.82    inference(subsumption_resolution,[],[f737,f54])).
% 3.67/0.82  fof(f737,plain,(
% 3.67/0.82    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | v2_struct_0(sK3)),
% 3.67/0.82    inference(subsumption_resolution,[],[f736,f55])).
% 3.67/0.82  fof(f736,plain,(
% 3.67/0.82    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 3.67/0.82    inference(subsumption_resolution,[],[f735,f56])).
% 3.67/0.82  fof(f735,plain,(
% 3.67/0.82    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 3.67/0.82    inference(subsumption_resolution,[],[f734,f62])).
% 3.67/0.82  fof(f734,plain,(
% 3.67/0.82    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 3.67/0.82    inference(subsumption_resolution,[],[f733,f63])).
% 3.67/0.82  fof(f733,plain,(
% 3.67/0.82    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 3.67/0.82    inference(subsumption_resolution,[],[f730,f64])).
% 3.67/0.82  fof(f730,plain,(
% 3.67/0.82    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 3.67/0.82    inference(superposition,[],[f482,f207])).
% 3.67/0.82  fof(f207,plain,(
% 3.67/0.82    k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6)),
% 3.67/0.82    inference(forward_demodulation,[],[f203,f177])).
% 3.67/0.82  fof(f177,plain,(
% 3.67/0.82    k2_tmap_1(sK2,sK3,sK6,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4))),
% 3.67/0.82    inference(resolution,[],[f167,f58])).
% 3.67/0.82  fof(f203,plain,(
% 3.67/0.82    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6)),
% 3.67/0.82    inference(resolution,[],[f202,f58])).
% 3.67/0.82  fof(f482,plain,(
% 3.67/0.82    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f481,f51])).
% 3.67/0.82  fof(f481,plain,(
% 3.67/0.82    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f480,f52])).
% 3.67/0.82  fof(f480,plain,(
% 3.67/0.82    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f479,f53])).
% 3.67/0.82  fof(f479,plain,(
% 3.67/0.82    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f478,f57])).
% 3.67/0.82  fof(f478,plain,(
% 3.67/0.82    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f477,f58])).
% 3.67/0.82  fof(f477,plain,(
% 3.67/0.82    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f476,f59])).
% 3.67/0.82  fof(f476,plain,(
% 3.67/0.82    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f475,f60])).
% 3.67/0.82  fof(f475,plain,(
% 3.67/0.82    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 3.67/0.82    inference(superposition,[],[f69,f61])).
% 3.67/0.82  fof(f69,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f22])).
% 3.67/0.82  fof(f22,plain,(
% 3.67/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(flattening,[],[f21])).
% 3.67/0.82  fof(f21,plain,(
% 3.67/0.82    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.82    inference(ennf_transformation,[],[f10])).
% 3.67/0.82  fof(f10,axiom,(
% 3.67/0.82    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).
% 3.67/0.82  fof(f361,plain,(
% 3.67/0.82    ~spl7_3 | spl7_11),
% 3.67/0.82    inference(avatar_split_clause,[],[f224,f358,f257])).
% 3.67/0.82  fof(f257,plain,(
% 3.67/0.82    spl7_3 <=> sP0(sK3,sK5,sK6,sK2,sK2)),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 3.67/0.82  fof(f224,plain,(
% 3.67/0.82    m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~sP0(sK3,sK5,sK6,sK2,sK2)),
% 3.67/0.82    inference(superposition,[],[f77,f208])).
% 3.67/0.82  fof(f77,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f47])).
% 3.67/0.82  fof(f47,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X4,X0,X3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2))) | ~sP0(X0,X1,X2,X3,X4))),
% 3.67/0.82    inference(rectify,[],[f46])).
% 3.67/0.82  fof(f46,plain,(
% 3.67/0.82    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP0(X1,X3,X4,X2,X0))),
% 3.67/0.82    inference(nnf_transformation,[],[f35])).
% 3.67/0.82  fof(f35,plain,(
% 3.67/0.82    ! [X1,X3,X4,X2,X0] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~sP0(X1,X3,X4,X2,X0))),
% 3.67/0.82    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.67/0.82  fof(f324,plain,(
% 3.67/0.82    ~spl7_1 | spl7_10),
% 3.67/0.82    inference(avatar_split_clause,[],[f215,f321,f241])).
% 3.67/0.82  fof(f241,plain,(
% 3.67/0.82    spl7_1 <=> sP0(sK3,sK4,sK6,sK2,sK2)),
% 3.67/0.82    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 3.67/0.82  fof(f215,plain,(
% 3.67/0.82    m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~sP0(sK3,sK4,sK6,sK2,sK2)),
% 3.67/0.82    inference(superposition,[],[f77,f207])).
% 3.67/0.82  fof(f297,plain,(
% 3.67/0.82    ~spl7_3 | spl7_8),
% 3.67/0.82    inference(avatar_split_clause,[],[f225,f294,f257])).
% 3.67/0.82  fof(f225,plain,(
% 3.67/0.82    v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~sP0(sK3,sK5,sK6,sK2,sK2)),
% 3.67/0.82    inference(superposition,[],[f76,f208])).
% 3.67/0.82  fof(f76,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,X3,X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f47])).
% 3.67/0.82  fof(f292,plain,(
% 3.67/0.82    ~spl7_1 | spl7_7),
% 3.67/0.82    inference(avatar_split_clause,[],[f216,f289,f241])).
% 3.67/0.82  fof(f216,plain,(
% 3.67/0.82    v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~sP0(sK3,sK4,sK6,sK2,sK2)),
% 3.67/0.82    inference(superposition,[],[f76,f207])).
% 3.67/0.82  fof(f271,plain,(
% 3.67/0.82    spl7_3),
% 3.67/0.82    inference(avatar_contradiction_clause,[],[f270])).
% 3.67/0.82  fof(f270,plain,(
% 3.67/0.82    $false | spl7_3),
% 3.67/0.82    inference(subsumption_resolution,[],[f269,f51])).
% 3.67/0.82  fof(f269,plain,(
% 3.67/0.82    v2_struct_0(sK2) | spl7_3),
% 3.67/0.82    inference(subsumption_resolution,[],[f268,f52])).
% 3.67/0.82  fof(f268,plain,(
% 3.67/0.82    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 3.67/0.82    inference(subsumption_resolution,[],[f267,f53])).
% 3.67/0.82  fof(f267,plain,(
% 3.67/0.82    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 3.67/0.82    inference(subsumption_resolution,[],[f266,f105])).
% 3.67/0.82  fof(f266,plain,(
% 3.67/0.82    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 3.67/0.82    inference(subsumption_resolution,[],[f265,f60])).
% 3.67/0.82  fof(f265,plain,(
% 3.67/0.82    ~m1_pre_topc(sK5,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 3.67/0.82    inference(resolution,[],[f259,f144])).
% 3.67/0.82  fof(f144,plain,(
% 3.67/0.82    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f143,f54])).
% 3.67/0.82  fof(f143,plain,(
% 3.67/0.82    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f142,f55])).
% 3.67/0.82  fof(f142,plain,(
% 3.67/0.82    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f141,f56])).
% 3.67/0.82  fof(f141,plain,(
% 3.67/0.82    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f140,f62])).
% 3.67/0.82  fof(f140,plain,(
% 3.67/0.82    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(subsumption_resolution,[],[f136,f63])).
% 3.67/0.82  fof(f136,plain,(
% 3.67/0.82    ( ! [X0,X1] : (sP0(sK3,X0,sK6,sK2,X1) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 3.67/0.82    inference(resolution,[],[f78,f64])).
% 3.67/0.82  fof(f78,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | sP0(X1,X3,X4,X2,X0) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f36])).
% 3.67/0.82  fof(f36,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4] : (sP0(X1,X3,X4,X2,X0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(definition_folding,[],[f30,f35])).
% 3.67/0.82  fof(f30,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.67/0.82    inference(flattening,[],[f29])).
% 3.67/0.82  fof(f29,plain,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.67/0.82    inference(ennf_transformation,[],[f9])).
% 3.67/0.82  fof(f9,axiom,(
% 3.67/0.82    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & m1_pre_topc(X2,X0) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4))))),
% 3.67/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).
% 3.67/0.82  fof(f259,plain,(
% 3.67/0.82    ~sP0(sK3,sK5,sK6,sK2,sK2) | spl7_3),
% 3.67/0.82    inference(avatar_component_clause,[],[f257])).
% 3.67/0.82  fof(f264,plain,(
% 3.67/0.82    ~spl7_3 | spl7_4),
% 3.67/0.82    inference(avatar_split_clause,[],[f226,f261,f257])).
% 3.67/0.82  fof(f226,plain,(
% 3.67/0.82    v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK5)) | ~sP0(sK3,sK5,sK6,sK2,sK2)),
% 3.67/0.82    inference(superposition,[],[f75,f208])).
% 3.67/0.82  fof(f75,plain,(
% 3.67/0.82    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,X3,X1,X2)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.67/0.82    inference(cnf_transformation,[],[f47])).
% 3.67/0.82  fof(f255,plain,(
% 3.67/0.82    spl7_1),
% 3.67/0.82    inference(avatar_contradiction_clause,[],[f254])).
% 3.67/0.82  fof(f254,plain,(
% 3.67/0.82    $false | spl7_1),
% 3.67/0.82    inference(subsumption_resolution,[],[f253,f51])).
% 3.67/0.82  fof(f253,plain,(
% 3.67/0.82    v2_struct_0(sK2) | spl7_1),
% 3.67/0.82    inference(subsumption_resolution,[],[f252,f52])).
% 3.67/0.82  fof(f252,plain,(
% 3.67/0.82    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_1),
% 3.67/0.82    inference(subsumption_resolution,[],[f251,f53])).
% 3.67/0.82  fof(f251,plain,(
% 3.67/0.82    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_1),
% 3.67/0.82    inference(subsumption_resolution,[],[f250,f105])).
% 3.67/0.82  fof(f250,plain,(
% 3.67/0.82    ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_1),
% 3.67/0.82    inference(subsumption_resolution,[],[f249,f58])).
% 3.67/0.82  fof(f249,plain,(
% 3.67/0.82    ~m1_pre_topc(sK4,sK2) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_1),
% 3.67/0.82    inference(resolution,[],[f243,f144])).
% 3.67/0.82  fof(f243,plain,(
% 3.67/0.82    ~sP0(sK3,sK4,sK6,sK2,sK2) | spl7_1),
% 3.67/0.82    inference(avatar_component_clause,[],[f241])).
% 3.67/0.82  fof(f248,plain,(
% 3.67/0.82    ~spl7_1 | spl7_2),
% 3.67/0.82    inference(avatar_split_clause,[],[f217,f245,f241])).
% 3.67/0.82  fof(f217,plain,(
% 3.67/0.82    v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~sP0(sK3,sK4,sK6,sK2,sK2)),
% 3.67/0.82    inference(superposition,[],[f75,f207])).
% 3.67/0.82  % SZS output end Proof for theBenchmark
% 3.67/0.82  % (1290)------------------------------
% 3.67/0.82  % (1290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.82  % (1290)Termination reason: Refutation
% 3.67/0.82  
% 3.67/0.82  % (1290)Memory used [KB]: 14456
% 3.67/0.82  % (1290)Time elapsed: 0.421 s
% 3.67/0.82  % (1290)------------------------------
% 3.67/0.82  % (1290)------------------------------
% 3.67/0.83  % (1264)Success in time 0.469 s
%------------------------------------------------------------------------------
