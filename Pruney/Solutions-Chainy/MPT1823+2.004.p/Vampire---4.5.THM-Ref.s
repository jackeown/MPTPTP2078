%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  203 (1477 expanded)
%              Number of leaves         :   25 ( 683 expanded)
%              Depth                    :   32
%              Number of atoms          : 1217 (19368 expanded)
%              Number of equality atoms :   69 (1440 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f599,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f476,f564,f567,f577,f581,f585,f598])).

fof(f598,plain,(
    ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f597])).

fof(f597,plain,
    ( $false
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f596,f54])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

% (32276)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f12,conjecture,(
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

fof(f596,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f595,f91])).

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

fof(f595,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_10 ),
    inference(resolution,[],[f594,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f594,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f593,f62])).

fof(f62,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f593,plain,
    ( ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f592,f63])).

fof(f63,plain,(
    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f592,plain,
    ( ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f591,f64])).

fof(f64,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f591,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(duplicate_literal_removal,[],[f590])).

fof(f590,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(resolution,[],[f589,f87])).

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

% (32275)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f589,plain,
    ( ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK6)
    | ~ spl7_10 ),
    inference(backward_demodulation,[],[f89,f475])).

fof(f475,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl7_10
  <=> sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f89,plain,(
    ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) ),
    inference(backward_demodulation,[],[f65,f61])).

fof(f61,plain,(
    sK2 = k1_tsep_1(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ~ r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) ),
    inference(cnf_transformation,[],[f44])).

fof(f585,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl7_14 ),
    inference(subsumption_resolution,[],[f583,f98])).

fof(f98,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f96,f66])).

fof(f96,plain,(
    l1_pre_topc(sK4) ),
    inference(subsumption_resolution,[],[f92,f53])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f68,f58])).

fof(f58,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f583,plain,
    ( ~ l1_struct_0(sK4)
    | spl7_14 ),
    inference(resolution,[],[f582,f121])).

fof(f121,plain,(
    ! [X0] :
      ( sP0(sK3,X0,sK6,sK2)
      | ~ l1_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f120,f90])).

fof(f90,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f66,f53])).

fof(f120,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP0(sK3,X0,sK6,sK2)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f119,f91])).

fof(f119,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP0(sK3,X0,sK6,sK2)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f118,f62])).

fof(f118,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP0(sK3,X0,sK6,sK2)
      | ~ v1_funct_1(sK6)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f114,f63])).

fof(f114,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | sP0(sK3,X0,sK6,sK2)
      | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK6)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f76,f64])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | sP0(X1,X3,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( sP0(X1,X3,X2,X0)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(definition_folding,[],[f28,f35])).

fof(f35,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f582,plain,
    ( ~ sP0(sK3,sK4,sK6,sK2)
    | spl7_14 ),
    inference(resolution,[],[f563,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X3,X2,X0] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ sP0(X1,X3,X2,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f563,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl7_14
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f581,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | spl7_13 ),
    inference(subsumption_resolution,[],[f579,f98])).

fof(f579,plain,
    ( ~ l1_struct_0(sK4)
    | spl7_13 ),
    inference(resolution,[],[f578,f121])).

fof(f578,plain,
    ( ~ sP0(sK3,sK4,sK6,sK2)
    | spl7_13 ),
    inference(resolution,[],[f559,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f559,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f557])).

fof(f557,plain,
    ( spl7_13
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f577,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | spl7_12 ),
    inference(subsumption_resolution,[],[f575,f98])).

fof(f575,plain,
    ( ~ l1_struct_0(sK4)
    | spl7_12 ),
    inference(resolution,[],[f574,f121])).

fof(f574,plain,
    ( ~ sP0(sK3,sK4,sK6,sK2)
    | spl7_12 ),
    inference(resolution,[],[f555,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f555,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl7_12
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f567,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | spl7_11 ),
    inference(subsumption_resolution,[],[f565,f99])).

fof(f99,plain,(
    l1_struct_0(sK5) ),
    inference(resolution,[],[f97,f66])).

fof(f97,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f93,f53])).

fof(f93,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f68,f60])).

fof(f60,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f565,plain,
    ( ~ l1_struct_0(sK5)
    | spl7_11 ),
    inference(resolution,[],[f551,f121])).

fof(f551,plain,
    ( ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl7_11
  <=> sP0(sK3,sK5,sK6,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f564,plain,
    ( ~ spl7_11
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_14
    | spl7_9 ),
    inference(avatar_split_clause,[],[f547,f469,f561,f557,f553,f549])).

fof(f469,plain,
    ( spl7_9
  <=> sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f547,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f546,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f546,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f545,f52])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f545,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f544,f53])).

fof(f544,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f543,f54])).

fof(f543,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f542,f55])).

fof(f55,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f542,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f541,f56])).

fof(f541,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f540,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f540,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f539,f58])).

fof(f539,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f538,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f538,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f513,f60])).

fof(f513,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ sP0(sK3,sK5,sK6,sK2)
    | spl7_9 ),
    inference(resolution,[],[f289,f471])).

fof(f471,plain,
    ( ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f469])).

fof(f289,plain,(
    ! [X6,X4,X8,X7,X5,X3,X9] :
      ( sP1(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
      | ~ v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(X4,X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP0(X3,X4,X8,X7) ) ),
    inference(subsumption_resolution,[],[f288,f73])).

fof(f288,plain,(
    ! [X6,X4,X8,X7,X5,X3,X9] :
      ( sP1(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9)
      | ~ v1_funct_1(k2_tmap_1(X7,X3,X8,X4))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
      | ~ v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(X4,X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP0(X3,X4,X8,X7) ) ),
    inference(subsumption_resolution,[],[f279,f74])).

fof(f279,plain,(
    ! [X6,X4,X8,X7,X5,X3,X9] :
      ( sP1(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9)
      | ~ v1_funct_2(k2_tmap_1(X7,X3,X8,X4),u1_struct_0(X4),u1_struct_0(X3))
      | ~ v1_funct_1(k2_tmap_1(X7,X3,X8,X4))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
      | ~ v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3))
      | ~ v1_funct_1(X9)
      | ~ m1_pre_topc(X4,X6)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ sP0(X3,X4,X8,X7) ) ),
    inference(resolution,[],[f84,f75])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f476,plain,
    ( ~ spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f467,f473,f469])).

fof(f467,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f466,f62])).

fof(f466,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f465,f63])).

fof(f465,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    inference(subsumption_resolution,[],[f464,f64])).

fof(f464,plain,
    ( sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) ),
    inference(resolution,[],[f448,f142])).

fof(f142,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X13),X14,k10_tmap_1(sK2,X13,sK4,sK5,X15,X16))
      | k10_tmap_1(sK2,X13,sK4,sK5,X15,X16) = X14
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X13))))
      | ~ v1_funct_2(X14,u1_struct_0(sK2),u1_struct_0(X13))
      | ~ v1_funct_1(X14)
      | ~ sP1(X13,sK5,sK4,sK2,X16,X15) ) ),
    inference(subsumption_resolution,[],[f141,f81])).

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

fof(f141,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X13),X14,k10_tmap_1(sK2,X13,sK4,sK5,X15,X16))
      | k10_tmap_1(sK2,X13,sK4,sK5,X15,X16) = X14
      | ~ v1_funct_1(k10_tmap_1(sK2,X13,sK4,sK5,X15,X16))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X13))))
      | ~ v1_funct_2(X14,u1_struct_0(sK2),u1_struct_0(X13))
      | ~ v1_funct_1(X14)
      | ~ sP1(X13,sK5,sK4,sK2,X16,X15) ) ),
    inference(subsumption_resolution,[],[f134,f106])).

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

fof(f134,plain,(
    ! [X14,X15,X13,X16] :
      ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(X13),X14,k10_tmap_1(sK2,X13,sK4,sK5,X15,X16))
      | k10_tmap_1(sK2,X13,sK4,sK5,X15,X16) = X14
      | ~ v1_funct_2(k10_tmap_1(sK2,X13,sK4,sK5,X15,X16),u1_struct_0(sK2),u1_struct_0(X13))
      | ~ v1_funct_1(k10_tmap_1(sK2,X13,sK4,sK5,X15,X16))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X13))))
      | ~ v1_funct_2(X14,u1_struct_0(sK2),u1_struct_0(X13))
      | ~ v1_funct_1(X14)
      | ~ sP1(X13,sK5,sK4,sK2,X16,X15) ) ),
    inference(resolution,[],[f77,f108])).

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

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f448,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) ),
    inference(forward_demodulation,[],[f447,f235])).

fof(f235,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6) ),
    inference(forward_demodulation,[],[f232,f178])).

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
    inference(resolution,[],[f72,f64])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f232,plain,(
    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6) ),
    inference(resolution,[],[f230,f60])).

fof(f230,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) ) ),
    inference(subsumption_resolution,[],[f229,f51])).

fof(f229,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f228,f52])).

fof(f228,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f227,f53])).

fof(f227,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f219,f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f218,f54])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f217,f55])).

fof(f217,plain,(
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
    inference(subsumption_resolution,[],[f216,f56])).

fof(f216,plain,(
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
    inference(subsumption_resolution,[],[f215,f62])).

fof(f215,plain,(
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
    inference(subsumption_resolution,[],[f211,f63])).

fof(f211,plain,(
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
    inference(resolution,[],[f70,f64])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f447,plain,(
    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) ),
    inference(subsumption_resolution,[],[f446,f54])).

fof(f446,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f445,f55])).

fof(f445,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f444,f56])).

fof(f444,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f443,f62])).

fof(f443,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f442,f63])).

fof(f442,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f437,f64])).

fof(f437,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(superposition,[],[f419,f234])).

fof(f234,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6) ),
    inference(forward_demodulation,[],[f231,f177])).

fof(f177,plain,(
    k2_tmap_1(sK2,sK3,sK6,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) ),
    inference(resolution,[],[f167,f58])).

fof(f231,plain,(
    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6) ),
    inference(resolution,[],[f230,f58])).

fof(f419,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f418,f51])).

fof(f418,plain,(
    ! [X0,X1] :
      ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f417,f52])).

fof(f417,plain,(
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
    inference(subsumption_resolution,[],[f416,f53])).

% (32286)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (32294)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (32285)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (32287)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (32280)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f416,plain,(
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
    inference(subsumption_resolution,[],[f415,f57])).

fof(f415,plain,(
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
    inference(subsumption_resolution,[],[f414,f58])).

fof(f414,plain,(
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
    inference(subsumption_resolution,[],[f413,f59])).

fof(f413,plain,(
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
    inference(subsumption_resolution,[],[f412,f60])).

fof(f412,plain,(
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
    inference(superposition,[],[f71,f61])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:29:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (32272)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (32297)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.48  % (32273)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (32277)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (32284)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (32291)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (32281)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (32290)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (32282)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (32278)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (32274)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (32283)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (32289)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (32279)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (32296)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (32297)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f599,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f476,f564,f567,f577,f581,f585,f598])).
% 0.20/0.51  fof(f598,plain,(
% 0.20/0.51    ~spl7_10),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f597])).
% 0.20/0.51  fof(f597,plain,(
% 0.20/0.51    $false | ~spl7_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f596,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ~v2_struct_0(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ((((~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6)) & sK2 = k1_tsep_1(sK2,sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f43,f42,f41,f40,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK2,X1,X2,X3,k2_tmap_1(sK2,X1,X4,X2),k2_tmap_1(sK2,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,X2,X3,k2_tmap_1(sK2,sK3,X4,X2),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,X2,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,X3,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,X3) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) & sK2 = k1_tsep_1(sK2,sK4,sK5) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ? [X4] : (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),X4,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,X4,sK4),k2_tmap_1(sK2,sK3,X4,sK5))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f12])).
% 0.20/0.51  % (32276)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  fof(f12,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).
% 0.20/0.51  fof(f596,plain,(
% 0.20/0.51    v2_struct_0(sK3) | ~spl7_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f595,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    l1_struct_0(sK3)),
% 0.20/0.51    inference(resolution,[],[f66,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    l1_pre_topc(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.51  fof(f595,plain,(
% 0.20/0.51    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl7_10),
% 0.20/0.51    inference(resolution,[],[f594,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.51  fof(f594,plain,(
% 0.20/0.51    v1_xboole_0(u1_struct_0(sK3)) | ~spl7_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f593,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    v1_funct_1(sK6)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f593,plain,(
% 0.20/0.51    ~v1_funct_1(sK6) | v1_xboole_0(u1_struct_0(sK3)) | ~spl7_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f592,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f592,plain,(
% 0.20/0.51    ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v1_xboole_0(u1_struct_0(sK3)) | ~spl7_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f591,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f591,plain,(
% 0.20/0.51    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v1_xboole_0(u1_struct_0(sK3)) | ~spl7_10),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f590])).
% 0.20/0.51  fof(f590,plain,(
% 0.20/0.51    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | ~spl7_10),
% 0.20/0.51    inference(resolution,[],[f589,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 0.20/0.51    inference(flattening,[],[f31])).
% 0.20/0.51  % (32275)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).
% 0.20/0.51  fof(f589,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,sK6) | ~spl7_10),
% 0.20/0.51    inference(backward_demodulation,[],[f89,f475])).
% 0.20/0.51  fof(f475,plain,(
% 0.20/0.51    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~spl7_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f473])).
% 0.20/0.51  fof(f473,plain,(
% 0.20/0.51    spl7_10 <=> sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))),
% 0.20/0.51    inference(backward_demodulation,[],[f65,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    sK2 = k1_tsep_1(sK2,sK4,sK5)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ~r1_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f585,plain,(
% 0.20/0.51    spl7_14),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f584])).
% 0.20/0.51  fof(f584,plain,(
% 0.20/0.51    $false | spl7_14),
% 0.20/0.51    inference(subsumption_resolution,[],[f583,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    l1_struct_0(sK4)),
% 0.20/0.51    inference(resolution,[],[f96,f66])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    l1_pre_topc(sK4)),
% 0.20/0.51    inference(subsumption_resolution,[],[f92,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    l1_pre_topc(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    l1_pre_topc(sK4) | ~l1_pre_topc(sK2)),
% 0.20/0.51    inference(resolution,[],[f68,f58])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    m1_pre_topc(sK4,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.51  fof(f583,plain,(
% 0.20/0.51    ~l1_struct_0(sK4) | spl7_14),
% 0.20/0.51    inference(resolution,[],[f582,f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    ( ! [X0] : (sP0(sK3,X0,sK6,sK2) | ~l1_struct_0(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f120,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    l1_struct_0(sK2)),
% 0.20/0.51    inference(resolution,[],[f66,f53])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | sP0(sK3,X0,sK6,sK2) | ~l1_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f119,f91])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | sP0(sK3,X0,sK6,sK2) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f118,f62])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | sP0(sK3,X0,sK6,sK2) | ~v1_funct_1(sK6) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f114,f63])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | sP0(sK3,X0,sK6,sK2) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 0.20/0.51    inference(resolution,[],[f76,f64])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | sP0(X1,X3,X2,X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (sP0(X1,X3,X2,X0) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(definition_folding,[],[f28,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X1,X3,X2,X0] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP0(X1,X3,X2,X0))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 0.20/0.51  fof(f582,plain,(
% 0.20/0.51    ~sP0(sK3,sK4,sK6,sK2) | spl7_14),
% 0.20/0.51    inference(resolution,[],[f563,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))) | ~sP0(X0,X1,X2,X3))),
% 0.20/0.51    inference(rectify,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X1,X3,X2,X0] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~sP0(X1,X3,X2,X0))),
% 0.20/0.51    inference(nnf_transformation,[],[f35])).
% 0.20/0.51  fof(f563,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | spl7_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f561])).
% 0.20/0.51  fof(f561,plain,(
% 0.20/0.51    spl7_14 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.51  fof(f581,plain,(
% 0.20/0.51    spl7_13),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f580])).
% 0.20/0.51  fof(f580,plain,(
% 0.20/0.51    $false | spl7_13),
% 0.20/0.51    inference(subsumption_resolution,[],[f579,f98])).
% 0.20/0.51  fof(f579,plain,(
% 0.20/0.51    ~l1_struct_0(sK4) | spl7_13),
% 0.20/0.51    inference(resolution,[],[f578,f121])).
% 0.20/0.51  fof(f578,plain,(
% 0.20/0.51    ~sP0(sK3,sK4,sK6,sK2) | spl7_13),
% 0.20/0.51    inference(resolution,[],[f559,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f559,plain,(
% 0.20/0.51    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | spl7_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f557])).
% 0.20/0.51  fof(f557,plain,(
% 0.20/0.51    spl7_13 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.51  fof(f577,plain,(
% 0.20/0.51    spl7_12),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f576])).
% 0.20/0.51  fof(f576,plain,(
% 0.20/0.51    $false | spl7_12),
% 0.20/0.51    inference(subsumption_resolution,[],[f575,f98])).
% 0.20/0.51  fof(f575,plain,(
% 0.20/0.51    ~l1_struct_0(sK4) | spl7_12),
% 0.20/0.51    inference(resolution,[],[f574,f121])).
% 0.20/0.51  fof(f574,plain,(
% 0.20/0.51    ~sP0(sK3,sK4,sK6,sK2) | spl7_12),
% 0.20/0.51    inference(resolution,[],[f555,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f46])).
% 0.20/0.51  fof(f555,plain,(
% 0.20/0.51    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | spl7_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f553])).
% 0.20/0.51  fof(f553,plain,(
% 0.20/0.51    spl7_12 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.51  fof(f567,plain,(
% 0.20/0.51    spl7_11),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f566])).
% 0.20/0.51  fof(f566,plain,(
% 0.20/0.51    $false | spl7_11),
% 0.20/0.51    inference(subsumption_resolution,[],[f565,f99])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    l1_struct_0(sK5)),
% 0.20/0.51    inference(resolution,[],[f97,f66])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    l1_pre_topc(sK5)),
% 0.20/0.51    inference(subsumption_resolution,[],[f93,f53])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    l1_pre_topc(sK5) | ~l1_pre_topc(sK2)),
% 0.20/0.51    inference(resolution,[],[f68,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    m1_pre_topc(sK5,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f565,plain,(
% 0.20/0.51    ~l1_struct_0(sK5) | spl7_11),
% 0.20/0.51    inference(resolution,[],[f551,f121])).
% 0.20/0.51  fof(f551,plain,(
% 0.20/0.51    ~sP0(sK3,sK5,sK6,sK2) | spl7_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f549])).
% 0.20/0.51  fof(f549,plain,(
% 0.20/0.51    spl7_11 <=> sP0(sK3,sK5,sK6,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.51  fof(f564,plain,(
% 0.20/0.51    ~spl7_11 | ~spl7_12 | ~spl7_13 | ~spl7_14 | spl7_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f547,f469,f561,f557,f553,f549])).
% 0.20/0.51  fof(f469,plain,(
% 0.20/0.51    spl7_9 <=> sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.51  fof(f547,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f546,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ~v2_struct_0(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f546,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f545,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    v2_pre_topc(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f545,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f544,f53])).
% 0.20/0.51  fof(f544,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f543,f54])).
% 0.20/0.51  fof(f543,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f542,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    v2_pre_topc(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f542,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f541,f56])).
% 0.20/0.51  fof(f541,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f540,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ~v2_struct_0(sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f540,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f539,f58])).
% 0.20/0.51  fof(f539,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f538,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ~v2_struct_0(sK5)),
% 0.20/0.51    inference(cnf_transformation,[],[f44])).
% 0.20/0.51  fof(f538,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(subsumption_resolution,[],[f513,f60])).
% 0.20/0.51  fof(f513,plain,(
% 0.20/0.51    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK6,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK6,sK4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK6,sK4)) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~sP0(sK3,sK5,sK6,sK2) | spl7_9),
% 0.20/0.51    inference(resolution,[],[f289,f471])).
% 0.20/0.51  fof(f471,plain,(
% 0.20/0.51    ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4)) | spl7_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f469])).
% 0.20/0.51  fof(f289,plain,(
% 0.20/0.51    ( ! [X6,X4,X8,X7,X5,X3,X9] : (sP1(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3)))) | ~v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3)) | ~v1_funct_1(X9) | ~m1_pre_topc(X4,X6) | v2_struct_0(X4) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP0(X3,X4,X8,X7)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f288,f73])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    ( ! [X6,X4,X8,X7,X5,X3,X9] : (sP1(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9) | ~v1_funct_1(k2_tmap_1(X7,X3,X8,X4)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3)))) | ~v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3)) | ~v1_funct_1(X9) | ~m1_pre_topc(X4,X6) | v2_struct_0(X4) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP0(X3,X4,X8,X7)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f279,f74])).
% 0.20/0.51  fof(f279,plain,(
% 0.20/0.51    ( ! [X6,X4,X8,X7,X5,X3,X9] : (sP1(X3,X4,X5,X6,k2_tmap_1(X7,X3,X8,X4),X9) | ~v1_funct_2(k2_tmap_1(X7,X3,X8,X4),u1_struct_0(X4),u1_struct_0(X3)) | ~v1_funct_1(k2_tmap_1(X7,X3,X8,X4)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3)))) | ~v1_funct_2(X9,u1_struct_0(X5),u1_struct_0(X3)) | ~v1_funct_1(X9) | ~m1_pre_topc(X4,X6) | v2_struct_0(X4) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X3) | ~v2_pre_topc(X3) | v2_struct_0(X3) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~sP0(X3,X4,X8,X7)) )),
% 0.20/0.51    inference(resolution,[],[f84,f75])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | sP1(X1,X3,X2,X0,X5,X4) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : (sP1(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(definition_folding,[],[f34,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP1(X1,X3,X2,X0,X5,X4))),
% 0.20/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).
% 0.20/0.51  fof(f476,plain,(
% 0.20/0.51    ~spl7_9 | spl7_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f467,f473,f469])).
% 0.20/0.51  fof(f467,plain,(
% 0.20/0.51    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f466,f62])).
% 0.20/0.51  fof(f466,plain,(
% 0.20/0.51    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f465,f63])).
% 0.20/0.51  fof(f465,plain,(
% 0.20/0.51    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 0.20/0.51    inference(subsumption_resolution,[],[f464,f64])).
% 0.20/0.51  fof(f464,plain,(
% 0.20/0.51    sK6 = k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~sP1(sK3,sK5,sK4,sK2,k2_tmap_1(sK2,sK3,sK6,sK5),k2_tmap_1(sK2,sK3,sK6,sK4))),
% 0.20/0.51    inference(resolution,[],[f448,f142])).
% 0.20/0.51  fof(f142,plain,(
% 0.20/0.51    ( ! [X14,X15,X13,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X13),X14,k10_tmap_1(sK2,X13,sK4,sK5,X15,X16)) | k10_tmap_1(sK2,X13,sK4,sK5,X15,X16) = X14 | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X14,u1_struct_0(sK2),u1_struct_0(X13)) | ~v1_funct_1(X14) | ~sP1(X13,sK5,sK4,sK2,X16,X15)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f141,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(k10_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP1(X0,X1,X2,X3,X4,X5))),
% 0.20/0.51    inference(rectify,[],[f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP1(X1,X3,X2,X0,X5,X4))),
% 0.20/0.51    inference(nnf_transformation,[],[f37])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    ( ! [X14,X15,X13,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X13),X14,k10_tmap_1(sK2,X13,sK4,sK5,X15,X16)) | k10_tmap_1(sK2,X13,sK4,sK5,X15,X16) = X14 | ~v1_funct_1(k10_tmap_1(sK2,X13,sK4,sK5,X15,X16)) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X14,u1_struct_0(sK2),u1_struct_0(X13)) | ~v1_funct_1(X14) | ~sP1(X13,sK5,sK4,sK2,X16,X15)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f134,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_funct_2(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),u1_struct_0(sK2),u1_struct_0(X0)) | ~sP1(X0,sK5,sK4,sK2,X2,X1)) )),
% 0.20/0.51    inference(superposition,[],[f82,f61])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X3,X0,X2,X1,X5,X4),u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X14,X15,X13,X16] : (~r2_funct_2(u1_struct_0(sK2),u1_struct_0(X13),X14,k10_tmap_1(sK2,X13,sK4,sK5,X15,X16)) | k10_tmap_1(sK2,X13,sK4,sK5,X15,X16) = X14 | ~v1_funct_2(k10_tmap_1(sK2,X13,sK4,sK5,X15,X16),u1_struct_0(sK2),u1_struct_0(X13)) | ~v1_funct_1(k10_tmap_1(sK2,X13,sK4,sK5,X15,X16)) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X13)))) | ~v1_funct_2(X14,u1_struct_0(sK2),u1_struct_0(X13)) | ~v1_funct_1(X14) | ~sP1(X13,sK5,sK4,sK2,X16,X15)) )),
% 0.20/0.51    inference(resolution,[],[f77,f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k10_tmap_1(sK2,X0,sK4,sK5,X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~sP1(X0,sK5,sK4,sK2,X2,X1)) )),
% 0.20/0.51    inference(superposition,[],[f83,f61])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f50])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.20/0.51  fof(f448,plain,(
% 0.20/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k2_tmap_1(sK2,sK3,sK6,sK5)))),
% 0.20/0.51    inference(forward_demodulation,[],[f447,f235])).
% 0.20/0.51  fof(f235,plain,(
% 0.20/0.51    k2_tmap_1(sK2,sK3,sK6,sK5) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6)),
% 0.20/0.51    inference(forward_demodulation,[],[f232,f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    k2_tmap_1(sK2,sK3,sK6,sK5) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5))),
% 0.20/0.51    inference(resolution,[],[f167,f60])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f166,f51])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f165,f52])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f164,f53])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f163,f54])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f162,f55])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f161,f56])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f160,f62])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f156,f63])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_tmap_1(sK2,sK3,sK6,X0) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(resolution,[],[f72,f64])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK5)) = k3_tmap_1(sK2,sK3,sK2,sK5,sK6)),
% 0.20/0.51    inference(resolution,[],[f230,f60])).
% 0.20/0.51  fof(f230,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f229,f51])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f228,f52])).
% 0.20/0.51  fof(f228,plain,(
% 0.20/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f227,f53])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f226])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2)) )),
% 0.20/0.51    inference(resolution,[],[f219,f67])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f218,f54])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f217,f55])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f216,f56])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f215,f62])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f211,f63])).
% 0.20/0.51  fof(f211,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(X0)) = k3_tmap_1(X1,sK3,sK2,X0,sK6) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.51    inference(resolution,[],[f70,f64])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 0.20/0.51  fof(f447,plain,(
% 0.20/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f446,f54])).
% 0.20/0.51  fof(f446,plain,(
% 0.20/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | v2_struct_0(sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f445,f55])).
% 0.20/0.51  fof(f445,plain,(
% 0.20/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f444,f56])).
% 0.20/0.51  fof(f444,plain,(
% 0.20/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f443,f62])).
% 0.20/0.51  fof(f443,plain,(
% 0.20/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f442,f63])).
% 0.20/0.51  fof(f442,plain,(
% 0.20/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.20/0.51    inference(subsumption_resolution,[],[f437,f64])).
% 0.20/0.51  fof(f437,plain,(
% 0.20/0.51    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK6,k10_tmap_1(sK2,sK3,sK4,sK5,k2_tmap_1(sK2,sK3,sK6,sK4),k3_tmap_1(sK2,sK3,sK2,sK5,sK6))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.20/0.51    inference(superposition,[],[f419,f234])).
% 0.20/0.51  fof(f234,plain,(
% 0.20/0.51    k2_tmap_1(sK2,sK3,sK6,sK4) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6)),
% 0.20/0.51    inference(forward_demodulation,[],[f231,f177])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    k2_tmap_1(sK2,sK3,sK6,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4))),
% 0.20/0.51    inference(resolution,[],[f167,f58])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK6,u1_struct_0(sK4)) = k3_tmap_1(sK2,sK3,sK2,sK4,sK6)),
% 0.20/0.51    inference(resolution,[],[f230,f58])).
% 0.20/0.51  fof(f419,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f418,f51])).
% 0.20/0.51  fof(f418,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f417,f52])).
% 0.20/0.51  fof(f417,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f416,f53])).
% 0.20/0.51  % (32286)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (32294)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (32285)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (32287)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (32280)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  fof(f416,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f415,f57])).
% 0.20/0.52  fof(f415,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f414,f58])).
% 0.20/0.52  fof(f414,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f413,f59])).
% 0.20/0.52  fof(f413,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f412,f60])).
% 0.20/0.52  fof(f412,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_funct_2(u1_struct_0(sK2),u1_struct_0(X0),X1,k10_tmap_1(sK2,X0,sK4,sK5,k3_tmap_1(sK2,X0,sK2,sK4,X1),k3_tmap_1(sK2,X0,sK2,sK5,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(X1) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.52    inference(superposition,[],[f71,f61])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (32297)------------------------------
% 0.20/0.52  % (32297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32297)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (32297)Memory used [KB]: 11385
% 0.20/0.52  % (32297)Time elapsed: 0.091 s
% 0.20/0.52  % (32297)------------------------------
% 0.20/0.52  % (32297)------------------------------
% 0.20/0.53  % (32295)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (32271)Success in time 0.16 s
%------------------------------------------------------------------------------
