%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 446 expanded)
%              Number of leaves         :   16 (  88 expanded)
%              Depth                    :   30
%              Number of atoms          :  979 (4929 expanded)
%              Number of equality atoms :   17 ( 245 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f90,f132,f137,f172,f179,f210])).

fof(f210,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f208,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( r1_tmap_1(X1,X0,X2,X4)
                          <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) )
                          & X4 = X5
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_pre_topc(X3,X1)
                  & v1_tsep_1(X3,X1)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X1)
                      & v1_tsep_1(X3,X1)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( X4 = X5
                             => ( r1_tmap_1(X1,X0,X2,X4)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & v1_tsep_1(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( X4 = X5
                           => ( r1_tmap_1(X1,X0,X2,X4)
                            <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(f208,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f207,f82])).

fof(f82,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_1
  <=> r1_tmap_1(sK1,sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f207,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f206,f78])).

fof(f78,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f40,f41])).

fof(f41,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f206,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f205,f42])).

fof(f42,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f205,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f204,f45])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f204,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f203,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f203,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f202,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f202,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f201,f47])).

fof(f47,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f201,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f200,f46])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f200,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f199,f51])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f198,f50])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f198,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f197,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f197,plain,
    ( v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f196,f54])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f181,f53])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f181,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | v2_struct_0(sK0)
    | spl7_2 ),
    inference(resolution,[],[f87,f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f87,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl7_2
  <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f179,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f147,f177])).

fof(f177,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f176,f49])).

fof(f176,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | v2_struct_0(sK1)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f175,f127])).

fof(f127,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_3
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f175,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f174,f51])).

fof(f174,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f173,f50])).

fof(f173,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f165,f42])).

fof(f165,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | v2_struct_0(sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f131,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK6(X0,X1,X2),X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              | ~ m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_4
  <=> ! [X0] :
        ( ~ m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f147,plain,
    ( m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_5
  <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f172,plain,
    ( ~ spl7_3
    | spl7_5 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f170,f92])).

fof(f92,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f91,f51])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f170,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl7_3
    | spl7_5 ),
    inference(resolution,[],[f169,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f169,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f168,f43])).

fof(f168,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_3
    | spl7_5 ),
    inference(resolution,[],[f167,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f167,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f166,f78])).

fof(f166,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl7_3
    | spl7_5 ),
    inference(resolution,[],[f163,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f163,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ spl7_3
    | spl7_5 ),
    inference(subsumption_resolution,[],[f162,f42])).

fof(f162,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl7_3
    | spl7_5 ),
    inference(resolution,[],[f161,f148])).

fof(f148,plain,
    ( ~ m1_connsp_2(u1_struct_0(sK3),sK1,sK4)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f146])).

fof(f161,plain,
    ( ! [X0] :
        ( m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f160,f157])).

fof(f157,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f156,f45])).

fof(f156,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f155,f44])).

fof(f44,plain,(
    v1_tsep_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f155,plain,
    ( v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f154,f50])).

fof(f154,plain,
    ( ~ v2_pre_topc(sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f142,f51])).

fof(f142,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v3_pre_topc(u1_struct_0(sK3),sK1)
    | ~ v1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f127,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f160,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(u1_struct_0(sK3),sK1,X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f159,f49])).

fof(f159,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(u1_struct_0(sK3),sK1,X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f158,f51])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(u1_struct_0(sK3),sK1,X0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f144,f50])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ v3_pre_topc(u1_struct_0(sK3),sK1)
        | ~ r2_hidden(X0,u1_struct_0(sK3))
        | m1_connsp_2(u1_struct_0(sK3),sK1,X0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f127,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f137,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f133,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | spl7_3 ),
    inference(resolution,[],[f128,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f128,plain,
    ( ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f132,plain,
    ( ~ spl7_3
    | spl7_4
    | spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f124,f85,f81,f130,f126])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f123,f49])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f121,f50])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2 ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(u1_struct_0(sK3),sK1,X0)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f114,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK6(X0,X1,X2),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f114,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(sK6(sK1,X1,X2),u1_struct_0(sK3))
        | ~ m1_connsp_2(sK6(sK1,X1,X2),sK1,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X2,sK1,X1) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f113,f49])).

fof(f113,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(sK6(sK1,X1,X2),u1_struct_0(sK3))
        | ~ m1_connsp_2(sK6(sK1,X1,X2),sK1,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X2,sK1,X1)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f112,f51])).

fof(f112,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(sK6(sK1,X1,X2),u1_struct_0(sK3))
        | ~ m1_connsp_2(sK6(sK1,X1,X2),sK1,sK4)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X2,sK1,X1)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f109,f50])).

fof(f109,plain,
    ( ! [X2,X1] :
        ( ~ r1_tarski(sK6(sK1,X1,X2),u1_struct_0(sK3))
        | ~ m1_connsp_2(sK6(sK1,X1,X2),sK1,sK4)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_connsp_2(X2,sK1,X1)
        | v2_struct_0(sK1) )
    | spl7_1
    | ~ spl7_2 ),
    inference(resolution,[],[f107,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f106,f83])).

fof(f83,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f105,f52])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f104,f78])).

fof(f104,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f103,f42])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f101,f43])).

fof(f101,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f100,f48])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f99,f47])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f98,f46])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f97,f51])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f96,f50])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f95,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f94,f54])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f93,f53])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK4,u1_struct_0(sK1))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ r1_tarski(X0,u1_struct_0(sK3))
        | ~ m1_connsp_2(X0,sK1,sK4)
        | v2_struct_0(sK0)
        | r1_tmap_1(sK1,sK0,sK2,sK4) )
    | ~ spl7_2 ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X6)
      | v2_struct_0(X0)
      | r1_tmap_1(X1,X0,X2,X6) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ r1_tarski(X4,u1_struct_0(X3))
      | ~ m1_connsp_2(X4,X1,X5)
      | X5 != X6
      | ~ r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)
      | r1_tmap_1(X1,X0,X2,X5) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X1,X0,X2,X5)
                              <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) )
                              | X5 != X6
                              | ~ m1_connsp_2(X4,X1,X5)
                              | ~ r1_tarski(X4,u1_struct_0(X3))
                              | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( X5 = X6
                                  & m1_connsp_2(X4,X1,X5)
                                  & r1_tarski(X4,u1_struct_0(X3)) )
                               => ( r1_tmap_1(X1,X0,X2,X5)
                                <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

fof(f86,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f90,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f89,f85,f81])).

fof(f89,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f38,f41])).

fof(f38,plain,
    ( r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f79,f85,f81])).

fof(f79,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(forward_demodulation,[],[f39,f41])).

fof(f39,plain,
    ( ~ r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5)
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (27217)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.45  % (27217)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f211,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f88,f90,f132,f137,f172,f179,f210])).
% 0.20/0.45  fof(f210,plain,(
% 0.20/0.45    ~spl7_1 | spl7_2),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f209])).
% 0.20/0.45  fof(f209,plain,(
% 0.20/0.45    $false | (~spl7_1 | spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f208,f52])).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((r1_tmap_1(X1,X0,X2,X4) <~> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) & X4 = X5) & m1_subset_1(X5,u1_struct_0(X3))) & m1_subset_1(X4,u1_struct_0(X1))) & (m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.45    inference(negated_conjecture,[],[f13])).
% 0.20/0.45  fof(f13,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & v1_tsep_1(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => (X4 = X5 => (r1_tmap_1(X1,X0,X2,X4) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)))))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).
% 0.20/0.45  fof(f208,plain,(
% 0.20/0.45    v2_struct_0(sK0) | (~spl7_1 | spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f207,f82])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    r1_tmap_1(sK1,sK0,sK2,sK4) | ~spl7_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f81])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    spl7_1 <=> r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.45  fof(f207,plain,(
% 0.20/0.45    ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f206,f78])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.45    inference(forward_demodulation,[],[f40,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    sK4 = sK5),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f206,plain,(
% 0.20/0.45    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f205,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    m1_subset_1(sK4,u1_struct_0(sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f205,plain,(
% 0.20/0.45    ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f204,f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    m1_pre_topc(sK3,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f204,plain,(
% 0.20/0.45    ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f203,f43])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ~v2_struct_0(sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f203,plain,(
% 0.20/0.45    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f202,f48])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f202,plain,(
% 0.20/0.45    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f201,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f201,plain,(
% 0.20/0.45    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f200,f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    v1_funct_1(sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f200,plain,(
% 0.20/0.45    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f199,f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    l1_pre_topc(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f199,plain,(
% 0.20/0.45    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f198,f50])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    v2_pre_topc(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f198,plain,(
% 0.20/0.45    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f197,f49])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ~v2_struct_0(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f197,plain,(
% 0.20/0.45    v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f196,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f196,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f181,f53])).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f181,plain,(
% 0.20/0.45    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tmap_1(sK1,sK0,sK2,sK4) | v2_struct_0(sK0) | spl7_2),
% 0.20/0.45    inference(resolution,[],[f87,f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(equality_resolution,[],[f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | spl7_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f85])).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    spl7_2 <=> r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.45  fof(f179,plain,(
% 0.20/0.45    ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f178])).
% 0.20/0.45  fof(f178,plain,(
% 0.20/0.45    $false | (~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.45    inference(subsumption_resolution,[],[f147,f177])).
% 0.20/0.45  fof(f177,plain,(
% 0.20/0.45    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | (~spl7_3 | ~spl7_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f176,f49])).
% 0.20/0.45  fof(f176,plain,(
% 0.20/0.45    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | v2_struct_0(sK1) | (~spl7_3 | ~spl7_4)),
% 0.20/0.45    inference(subsumption_resolution,[],[f175,f127])).
% 0.20/0.45  fof(f127,plain,(
% 0.20/0.45    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl7_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f126])).
% 0.20/0.45  fof(f126,plain,(
% 0.20/0.45    spl7_3 <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.45  fof(f175,plain,(
% 0.20/0.45    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~spl7_4),
% 0.20/0.45    inference(subsumption_resolution,[],[f174,f51])).
% 0.20/0.45  fof(f174,plain,(
% 0.20/0.45    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~spl7_4),
% 0.20/0.45    inference(subsumption_resolution,[],[f173,f50])).
% 0.20/0.45  fof(f173,plain,(
% 0.20/0.45    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~spl7_4),
% 0.20/0.45    inference(subsumption_resolution,[],[f165,f42])).
% 0.20/0.45  fof(f165,plain,(
% 0.20/0.45    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | v2_struct_0(sK1) | ~spl7_4),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f164])).
% 0.20/0.45  fof(f164,plain,(
% 0.20/0.45    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | v2_struct_0(sK1) | ~spl7_4),
% 0.20/0.45    inference(resolution,[],[f131,f61])).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_connsp_2(sK6(X0,X1,X2),X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((? [X3] : ((r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.20/0.45  fof(f131,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl7_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f130])).
% 0.20/0.45  fof(f130,plain,(
% 0.20/0.45    spl7_4 <=> ! [X0] : (~m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK1)))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.45  fof(f147,plain,(
% 0.20/0.45    m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | ~spl7_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f146])).
% 0.20/0.45  fof(f146,plain,(
% 0.20/0.45    spl7_5 <=> m1_connsp_2(u1_struct_0(sK3),sK1,sK4)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.45  fof(f172,plain,(
% 0.20/0.45    ~spl7_3 | spl7_5),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f171])).
% 0.20/0.45  fof(f171,plain,(
% 0.20/0.45    $false | (~spl7_3 | spl7_5)),
% 0.20/0.45    inference(subsumption_resolution,[],[f170,f92])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    l1_pre_topc(sK3)),
% 0.20/0.45    inference(subsumption_resolution,[],[f91,f51])).
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    ~l1_pre_topc(sK1) | l1_pre_topc(sK3)),
% 0.20/0.45    inference(resolution,[],[f45,f56])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.45  fof(f170,plain,(
% 0.20/0.45    ~l1_pre_topc(sK3) | (~spl7_3 | spl7_5)),
% 0.20/0.45    inference(resolution,[],[f169,f55])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.45  fof(f169,plain,(
% 0.20/0.45    ~l1_struct_0(sK3) | (~spl7_3 | spl7_5)),
% 0.20/0.45    inference(subsumption_resolution,[],[f168,f43])).
% 0.20/0.45  fof(f168,plain,(
% 0.20/0.45    ~l1_struct_0(sK3) | v2_struct_0(sK3) | (~spl7_3 | spl7_5)),
% 0.20/0.45    inference(resolution,[],[f167,f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.45  fof(f167,plain,(
% 0.20/0.45    v1_xboole_0(u1_struct_0(sK3)) | (~spl7_3 | spl7_5)),
% 0.20/0.45    inference(subsumption_resolution,[],[f166,f78])).
% 0.20/0.45  fof(f166,plain,(
% 0.20/0.45    v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl7_3 | spl7_5)),
% 0.20/0.45    inference(resolution,[],[f163,f71])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.45  fof(f163,plain,(
% 0.20/0.45    ~r2_hidden(sK4,u1_struct_0(sK3)) | (~spl7_3 | spl7_5)),
% 0.20/0.45    inference(subsumption_resolution,[],[f162,f42])).
% 0.20/0.45  fof(f162,plain,(
% 0.20/0.45    ~r2_hidden(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | (~spl7_3 | spl7_5)),
% 0.20/0.45    inference(resolution,[],[f161,f148])).
% 0.20/0.45  fof(f148,plain,(
% 0.20/0.45    ~m1_connsp_2(u1_struct_0(sK3),sK1,sK4) | spl7_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f146])).
% 0.20/0.45  fof(f161,plain,(
% 0.20/0.45    ( ! [X0] : (m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~r2_hidden(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK1))) ) | ~spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f160,f157])).
% 0.20/0.45  fof(f157,plain,(
% 0.20/0.45    v3_pre_topc(u1_struct_0(sK3),sK1) | ~spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f156,f45])).
% 0.20/0.45  fof(f156,plain,(
% 0.20/0.45    v3_pre_topc(u1_struct_0(sK3),sK1) | ~m1_pre_topc(sK3,sK1) | ~spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f155,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    v1_tsep_1(sK3,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f155,plain,(
% 0.20/0.45    v3_pre_topc(u1_struct_0(sK3),sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK3,sK1) | ~spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f154,f50])).
% 0.20/0.45  fof(f154,plain,(
% 0.20/0.45    ~v2_pre_topc(sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK3,sK1) | ~spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f142,f51])).
% 0.20/0.45  fof(f142,plain,(
% 0.20/0.45    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v3_pre_topc(u1_struct_0(sK3),sK1) | ~v1_tsep_1(sK3,sK1) | ~m1_pre_topc(sK3,sK1) | ~spl7_3),
% 0.20/0.45    inference(resolution,[],[f127,f77])).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.45    inference(equality_resolution,[],[f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X0)) ) | ~spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f159,f49])).
% 0.20/0.45  fof(f159,plain,(
% 0.20/0.45    ( ! [X0] : (v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X0)) ) | ~spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f158,f51])).
% 0.20/0.45  fof(f158,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X0)) ) | ~spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f144,f50])).
% 0.20/0.45  fof(f144,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~v3_pre_topc(u1_struct_0(sK3),sK1) | ~r2_hidden(X0,u1_struct_0(sK3)) | m1_connsp_2(u1_struct_0(sK3),sK1,X0)) ) | ~spl7_3),
% 0.20/0.45    inference(resolution,[],[f127,f64])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    spl7_3),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.45  fof(f136,plain,(
% 0.20/0.45    $false | spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f135,f51])).
% 0.20/0.45  fof(f135,plain,(
% 0.20/0.45    ~l1_pre_topc(sK1) | spl7_3),
% 0.20/0.45    inference(subsumption_resolution,[],[f133,f45])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    ~m1_pre_topc(sK3,sK1) | ~l1_pre_topc(sK1) | spl7_3),
% 0.20/0.45    inference(resolution,[],[f128,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.45  fof(f128,plain,(
% 0.20/0.45    ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl7_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f126])).
% 0.20/0.45  fof(f132,plain,(
% 0.20/0.45    ~spl7_3 | spl7_4 | spl7_1 | ~spl7_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f124,f85,f81,f130,f126])).
% 0.20/0.45  fof(f124,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f123,f49])).
% 0.20/0.45  fof(f123,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f122,f51])).
% 0.20/0.45  fof(f122,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f121,f50])).
% 0.20/0.45  fof(f121,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f120])).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_connsp_2(sK6(sK1,X0,u1_struct_0(sK3)),sK1,sK4) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | ~m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(u1_struct_0(sK3),sK1,X0) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(resolution,[],[f114,f63])).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(sK6(X0,X1,X2),X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f114,plain,(
% 0.20/0.45    ( ! [X2,X1] : (~r1_tarski(sK6(sK1,X1,X2),u1_struct_0(sK3)) | ~m1_connsp_2(sK6(sK1,X1,X2),sK1,sK4) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X2,sK1,X1)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f113,f49])).
% 0.20/0.45  fof(f113,plain,(
% 0.20/0.45    ( ! [X2,X1] : (~r1_tarski(sK6(sK1,X1,X2),u1_struct_0(sK3)) | ~m1_connsp_2(sK6(sK1,X1,X2),sK1,sK4) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X2,sK1,X1) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f112,f51])).
% 0.20/0.45  fof(f112,plain,(
% 0.20/0.45    ( ! [X2,X1] : (~r1_tarski(sK6(sK1,X1,X2),u1_struct_0(sK3)) | ~m1_connsp_2(sK6(sK1,X1,X2),sK1,sK4) | ~l1_pre_topc(sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X2,sK1,X1) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f109,f50])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    ( ! [X2,X1] : (~r1_tarski(sK6(sK1,X1,X2),u1_struct_0(sK3)) | ~m1_connsp_2(sK6(sK1,X1,X2),sK1,sK4) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_connsp_2(X2,sK1,X1) | v2_struct_0(sK1)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(resolution,[],[f107,f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f107,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4)) ) | (spl7_1 | ~spl7_2)),
% 0.20/0.45    inference(subsumption_resolution,[],[f106,f83])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ~r1_tmap_1(sK1,sK0,sK2,sK4) | spl7_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f81])).
% 0.20/0.45  fof(f106,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f105,f52])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f104,f78])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f103,f42])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f102,f45])).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f101,f43])).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    ( ! [X0] : (v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f100,f48])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f99,f47])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f98,f46])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f97,f51])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f96,f50])).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f95,f49])).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    ( ! [X0] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f94,f54])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(subsumption_resolution,[],[f93,f53])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK4,u1_struct_0(sK1)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r1_tarski(X0,u1_struct_0(sK3)) | ~m1_connsp_2(X0,sK1,sK4) | v2_struct_0(sK0) | r1_tmap_1(sK1,sK0,sK2,sK4)) ) | ~spl7_2),
% 0.20/0.45    inference(resolution,[],[f86,f75])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X6) | v2_struct_0(X0) | r1_tmap_1(X1,X0,X2,X6)) )),
% 0.20/0.45    inference(equality_resolution,[],[f66])).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_connsp_2(X4,X1,X5) | X5 != X6 | ~r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6) | r1_tmap_1(X1,X0,X2,X5)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6)) | (X5 != X6 | ~m1_connsp_2(X4,X1,X5) | ~r1_tarski(X4,u1_struct_0(X3)))) | ~m1_subset_1(X6,u1_struct_0(X3))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X3)) => ((X5 = X6 & m1_connsp_2(X4,X1,X5) & r1_tarski(X4,u1_struct_0(X3))) => (r1_tmap_1(X1,X0,X2,X5) <=> r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X6))))))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~spl7_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f85])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    spl7_1 | spl7_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f89,f85,f81])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.45    inference(forward_demodulation,[],[f38,f41])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    ~spl7_1 | ~spl7_2),
% 0.20/0.45    inference(avatar_split_clause,[],[f79,f85,f81])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK4) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.45    inference(forward_demodulation,[],[f39,f41])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ~r1_tmap_1(sK3,sK0,k2_tmap_1(sK1,sK0,sK2,sK3),sK5) | ~r1_tmap_1(sK1,sK0,sK2,sK4)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (27217)------------------------------
% 0.20/0.45  % (27217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (27217)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (27217)Memory used [KB]: 10746
% 0.20/0.45  % (27217)Time elapsed: 0.058 s
% 0.20/0.45  % (27217)------------------------------
% 0.20/0.45  % (27217)------------------------------
% 0.20/0.45  % (27212)Success in time 0.098 s
%------------------------------------------------------------------------------
