%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:44 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  230 (2581 expanded)
%              Number of leaves         :   37 ( 544 expanded)
%              Depth                    :   19
%              Number of atoms          : 1033 (45150 expanded)
%              Number of equality atoms :   30 (1896 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f105,f309,f323,f335,f337,f339,f378,f400,f406,f408,f439,f465,f538,f563,f567,f703,f745,f794,f896,f990,f1000,f1002,f1004,f1047,f1121,f1223,f1239,f1343])).

fof(f1343,plain,
    ( ~ spl7_23
    | ~ spl7_56 ),
    inference(avatar_contradiction_clause,[],[f1341])).

fof(f1341,plain,
    ( $false
    | ~ spl7_23
    | ~ spl7_56 ),
    inference(resolution,[],[f987,f562])).

fof(f562,plain,
    ( sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl7_23
  <=> sP6(sK2,sK4,sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f987,plain,
    ( ! [X8] : ~ sP6(sK2,X8,sK3,sK1,sK0)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f986])).

fof(f986,plain,
    ( spl7_56
  <=> ! [X8] : ~ sP6(sK2,X8,sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f1239,plain,
    ( ~ spl7_52
    | ~ spl7_53
    | ~ spl7_54
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_51
    | spl7_2 ),
    inference(avatar_split_clause,[],[f1238,f97,f963,f301,f297,f293,f289,f975,f971,f967])).

fof(f967,plain,
    ( spl7_52
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f971,plain,
    ( spl7_53
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f975,plain,
    ( spl7_54
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f289,plain,
    ( spl7_8
  <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f293,plain,
    ( spl7_9
  <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f297,plain,
    ( spl7_10
  <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f301,plain,
    ( spl7_11
  <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f963,plain,
    ( spl7_51
  <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f97,plain,
    ( spl7_2
  <=> sP5(sK4,sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1238,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1237,f172])).

fof(f172,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3)) ),
    inference(resolution,[],[f167,f54])).

fof(f54,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
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
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( r4_tsep_1(X0,X3,X4)
                            & k1_tsep_1(X0,X3,X4) = X0 )
                         => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(X2,X0,X1)
                              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X2) )
                          <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

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
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f55,f58,f59,f60,f61,f62,f63,f56,f166])).

fof(f166,plain,(
    ! [X0] :
      ( k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f155,f130])).

fof(f130,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0) ),
    inference(global_subsumption,[],[f55,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f91,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f80,f57])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f56,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f62,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f1237,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1236,f171])).

fof(f171,plain,(
    k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4)) ),
    inference(resolution,[],[f167,f50])).

fof(f50,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1236,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1235,f171])).

fof(f1235,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1234,f171])).

fof(f1234,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1233,f171])).

fof(f1233,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1232,f172])).

fof(f1232,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1231,f172])).

fof(f1231,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(forward_demodulation,[],[f1230,f172])).

fof(f1230,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_2 ),
    inference(resolution,[],[f104,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X3,X2,X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f104,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1223,plain,
    ( spl7_45
    | ~ spl7_54 ),
    inference(avatar_contradiction_clause,[],[f1222])).

fof(f1222,plain,
    ( $false
    | spl7_45
    | ~ spl7_54 ),
    inference(resolution,[],[f1199,f976])).

fof(f976,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f975])).

fof(f1199,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl7_45 ),
    inference(forward_demodulation,[],[f699,f172])).

fof(f699,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | spl7_45 ),
    inference(avatar_component_clause,[],[f698])).

fof(f698,plain,
    ( spl7_45
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1121,plain,
    ( spl7_42
    | ~ spl7_52 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | spl7_42
    | ~ spl7_52 ),
    inference(resolution,[],[f968,f1028])).

fof(f1028,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_42 ),
    inference(forward_demodulation,[],[f620,f172])).

fof(f620,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | spl7_42 ),
    inference(avatar_component_clause,[],[f619])).

fof(f619,plain,
    ( spl7_42
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f968,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f967])).

fof(f1047,plain,
    ( ~ spl7_2
    | spl7_46 ),
    inference(avatar_contradiction_clause,[],[f1046])).

fof(f1046,plain,
    ( $false
    | ~ spl7_2
    | spl7_46 ),
    inference(resolution,[],[f922,f98])).

fof(f98,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f922,plain,
    ( ! [X3] : ~ sP5(X3,sK3,sK2,sK1,sK0)
    | spl7_46 ),
    inference(resolution,[],[f702,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f702,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | spl7_46 ),
    inference(avatar_component_clause,[],[f701])).

fof(f701,plain,
    ( spl7_46
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f1004,plain,
    ( ~ spl7_15
    | ~ spl7_47
    | ~ spl7_17
    | spl7_54 ),
    inference(avatar_split_clause,[],[f1003,f975,f333,f743,f327])).

fof(f327,plain,
    ( spl7_15
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f743,plain,
    ( spl7_47
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f333,plain,
    ( spl7_17
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f1003,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f55,f56,f57,f942])).

fof(f942,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f90,f172])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f1002,plain,
    ( ~ spl7_15
    | ~ spl7_47
    | ~ spl7_17
    | spl7_52 ),
    inference(avatar_split_clause,[],[f1001,f967,f333,f743,f327])).

fof(f1001,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f55,f56,f57,f941])).

fof(f941,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f89,f172])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1000,plain,
    ( ~ spl7_15
    | ~ spl7_47
    | ~ spl7_17
    | spl7_51 ),
    inference(avatar_split_clause,[],[f999,f963,f333,f743,f327])).

fof(f999,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f55,f56,f57,f940])).

fof(f940,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f88,f172])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f990,plain,
    ( spl7_56
    | spl7_53 ),
    inference(avatar_split_clause,[],[f934,f971,f986])).

fof(f934,plain,(
    ! [X10] :
      ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)
      | ~ sP6(sK2,X10,sK3,sK1,sK0) ) ),
    inference(superposition,[],[f69,f172])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ sP6(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
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
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(f896,plain,(
    spl7_27 ),
    inference(avatar_contradiction_clause,[],[f895])).

fof(f895,plain,
    ( $false
    | spl7_27 ),
    inference(resolution,[],[f453,f57])).

fof(f453,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl7_27 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl7_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f794,plain,(
    spl7_47 ),
    inference(avatar_contradiction_clause,[],[f793])).

fof(f793,plain,
    ( $false
    | spl7_47 ),
    inference(resolution,[],[f769,f109])).

fof(f109,plain,(
    l1_pre_topc(sK3) ),
    inference(global_subsumption,[],[f63,f107])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f65,f54])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f769,plain,
    ( ~ l1_pre_topc(sK3)
    | spl7_47 ),
    inference(resolution,[],[f744,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f744,plain,
    ( ~ l1_struct_0(sK3)
    | spl7_47 ),
    inference(avatar_component_clause,[],[f743])).

fof(f745,plain,
    ( ~ spl7_15
    | ~ spl7_47
    | ~ spl7_27
    | ~ spl7_26
    | ~ spl7_25
    | ~ spl7_17
    | spl7_33 ),
    inference(avatar_split_clause,[],[f737,f584,f333,f446,f449,f452,f743,f327])).

fof(f449,plain,
    ( spl7_26
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f446,plain,
    ( spl7_25
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f584,plain,
    ( spl7_33
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f737,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK0)
    | spl7_33 ),
    inference(resolution,[],[f585,f88])).

fof(f585,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_33 ),
    inference(avatar_component_clause,[],[f584])).

fof(f703,plain,
    ( ~ spl7_33
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_42
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | spl7_23 ),
    inference(avatar_split_clause,[],[f696,f404,f301,f297,f293,f289,f619,f701,f698,f584])).

fof(f696,plain,
    ( ~ m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_23 ),
    inference(forward_demodulation,[],[f695,f171])).

fof(f695,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
    | ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_23 ),
    inference(forward_demodulation,[],[f694,f171])).

fof(f694,plain,
    ( ~ v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_23 ),
    inference(forward_demodulation,[],[f693,f171])).

fof(f693,plain,
    ( ~ v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_23 ),
    inference(forward_demodulation,[],[f692,f171])).

fof(f692,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | spl7_23 ),
    inference(resolution,[],[f405,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP6(X4,X3,X2,X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f405,plain,
    ( ~ sP6(sK2,sK4,sK3,sK1,sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f404])).

fof(f567,plain,
    ( ~ spl7_14
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(resolution,[],[f562,f320])).

fof(f320,plain,
    ( ! [X12] : ~ sP6(sK2,sK4,X12,sK1,sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl7_14
  <=> ! [X12] : ~ sP6(sK2,sK4,X12,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f563,plain,
    ( ~ spl7_1
    | spl7_23 ),
    inference(avatar_split_clause,[],[f561,f404,f94])).

fof(f94,plain,
    ( spl7_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f561,plain,
    ( sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f55,f58,f59,f60,f56,f57,f554])).

fof(f554,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f553])).

fof(f553,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | sP6(sK2,sK4,sK3,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(superposition,[],[f257,f175])).

fof(f175,plain,(
    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(forward_demodulation,[],[f173,f123])).

fof(f123,plain,(
    sK2 = k7_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f110,f120])).

fof(f120,plain,
    ( sK2 = k7_relat_1(sK2,u1_struct_0(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f119,f115])).

fof(f115,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f85,f57])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | k7_relat_1(X0,X1) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = X0
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f81,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f110,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f84,f57])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f173,plain,(
    k7_relat_1(sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0) ),
    inference(resolution,[],[f167,f144])).

fof(f144,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(global_subsumption,[],[f49,f53,f61,f63,f50,f54,f142])).

fof(f142,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f87,f51])).

fof(f51,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
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

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | sP6(X1,sK4,sK3,X0,sK0)
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) ) ),
    inference(global_subsumption,[],[f49,f53,f61,f62,f63,f50,f54,f52,f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | sP6(X1,sK4,sK3,X0,sK0)
      | ~ v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0))
      | ~ v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0))
      | ~ v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f75,f51])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP6(X4,X3,X2,X1,X0)
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    r4_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f538,plain,(
    spl7_26 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | spl7_26 ),
    inference(resolution,[],[f450,f56])).

fof(f450,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f449])).

fof(f465,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | spl7_25 ),
    inference(resolution,[],[f447,f55])).

fof(f447,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_25 ),
    inference(avatar_component_clause,[],[f446])).

fof(f439,plain,
    ( ~ spl7_2
    | ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_12 ),
    inference(resolution,[],[f306,f98])).

fof(f306,plain,
    ( ! [X4] : ~ sP5(sK4,X4,sK2,sK1,sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl7_12
  <=> ! [X4] : ~ sP5(sK4,X4,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f408,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | spl7_17 ),
    inference(resolution,[],[f369,f60])).

fof(f369,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_17 ),
    inference(resolution,[],[f334,f64])).

fof(f334,plain,
    ( ~ l1_struct_0(sK1)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f333])).

fof(f406,plain,
    ( ~ spl7_23
    | spl7_1 ),
    inference(avatar_split_clause,[],[f402,f94,f404])).

fof(f402,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ sP6(sK2,sK4,sK3,sK1,sK0) ),
    inference(global_subsumption,[],[f55,f58,f59,f60,f56,f57,f401])).

fof(f401,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ sP6(sK2,sK4,sK3,sK1,sK0) ),
    inference(superposition,[],[f224,f175])).

fof(f224,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ sP6(X1,sK4,sK3,X0,sK0) ) ),
    inference(global_subsumption,[],[f49,f53,f61,f62,f63,f50,f54,f52,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK4)
      | ~ m1_pre_topc(sK4,sK0)
      | ~ r4_tsep_1(sK0,sK3,sK4)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
      | ~ sP6(X1,sK4,sK3,X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f78,f51])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ sP6(X4,X3,X2,X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f400,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | spl7_16 ),
    inference(resolution,[],[f361,f108])).

fof(f108,plain,(
    l1_pre_topc(sK4) ),
    inference(global_subsumption,[],[f63,f106])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK4) ),
    inference(resolution,[],[f65,f50])).

fof(f361,plain,
    ( ~ l1_pre_topc(sK4)
    | spl7_16 ),
    inference(resolution,[],[f331,f64])).

fof(f331,plain,
    ( ~ l1_struct_0(sK4)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl7_16
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f378,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl7_15 ),
    inference(resolution,[],[f356,f63])).

fof(f356,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_15 ),
    inference(resolution,[],[f328,f64])).

fof(f328,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f327])).

fof(f339,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | spl7_11 ),
    inference(avatar_split_clause,[],[f338,f301,f333,f330,f327])).

fof(f338,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f55,f56,f57,f278])).

fof(f278,plain,
    ( m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f90,f171])).

fof(f337,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | spl7_9 ),
    inference(avatar_split_clause,[],[f336,f293,f333,f330,f327])).

fof(f336,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f55,f56,f57,f277])).

fof(f277,plain,
    ( v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f89,f171])).

fof(f335,plain,
    ( ~ spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | spl7_8 ),
    inference(avatar_split_clause,[],[f325,f289,f333,f330,f327])).

fof(f325,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f55,f56,f57,f276])).

fof(f276,plain,
    ( v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f88,f171])).

fof(f323,plain,
    ( spl7_14
    | spl7_10 ),
    inference(avatar_split_clause,[],[f274,f297,f319])).

fof(f274,plain,(
    ! [X14] :
      ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
      | ~ sP6(sK2,sK4,X14,sK1,sK0) ) ),
    inference(superposition,[],[f73,f171])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
      | ~ sP6(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f309,plain,
    ( spl7_12
    | spl7_10 ),
    inference(avatar_split_clause,[],[f266,f297,f305])).

fof(f266,plain,(
    ! [X6] :
      ( v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)
      | ~ sP5(sK4,X6,sK2,sK1,sK0) ) ),
    inference(superposition,[],[f42,f171])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f105,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f102,f97,f94])).

fof(f102,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f92,f100,f101,f44])).

fof(f44,plain,
    ( ~ sP5(sK4,sK3,sK2,sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f101,plain,(
    v1_funct_1(sK2) ),
    inference(global_subsumption,[],[f55])).

fof(f100,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(global_subsumption,[],[f56])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(global_subsumption,[],[f57])).

fof(f99,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f47,f97,f94])).

fof(f47,plain,
    ( sP5(sK4,sK3,sK2,sK1,sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.48  % (12766)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.48  % (12758)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.49  % (12767)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.50  % (12752)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.50  % (12753)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (12754)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (12755)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (12753)Refutation not found, incomplete strategy% (12753)------------------------------
% 0.22/0.51  % (12753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12753)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12753)Memory used [KB]: 10746
% 0.22/0.51  % (12753)Time elapsed: 0.092 s
% 0.22/0.51  % (12753)------------------------------
% 0.22/0.51  % (12753)------------------------------
% 0.22/0.51  % (12751)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (12763)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (12757)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (12761)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.51  % (12771)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (12757)Refutation not found, incomplete strategy% (12757)------------------------------
% 0.22/0.51  % (12757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12757)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12757)Memory used [KB]: 6268
% 0.22/0.51  % (12757)Time elapsed: 0.091 s
% 0.22/0.51  % (12757)------------------------------
% 0.22/0.51  % (12757)------------------------------
% 0.22/0.52  % (12769)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (12768)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (12770)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (12765)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (12756)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (12773)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (12760)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (12766)Refutation not found, incomplete strategy% (12766)------------------------------
% 0.22/0.52  % (12766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12766)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (12766)Memory used [KB]: 2302
% 0.22/0.52  % (12766)Time elapsed: 0.106 s
% 0.22/0.52  % (12766)------------------------------
% 0.22/0.52  % (12766)------------------------------
% 0.22/0.53  % (12762)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (12773)Refutation not found, incomplete strategy% (12773)------------------------------
% 0.22/0.53  % (12773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12759)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  % (12764)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.53  % (12773)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12773)Memory used [KB]: 10746
% 0.22/0.53  % (12773)Time elapsed: 0.115 s
% 0.22/0.53  % (12773)------------------------------
% 0.22/0.53  % (12773)------------------------------
% 0.22/0.53  % (12750)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.54  % (12758)Refutation not found, incomplete strategy% (12758)------------------------------
% 0.22/0.54  % (12758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12758)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12758)Memory used [KB]: 11385
% 0.22/0.54  % (12758)Time elapsed: 0.091 s
% 0.22/0.54  % (12758)------------------------------
% 0.22/0.54  % (12758)------------------------------
% 0.22/0.54  % (12772)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.62/0.57  % (12760)Refutation not found, incomplete strategy% (12760)------------------------------
% 1.62/0.57  % (12760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.57  % (12760)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.57  
% 1.62/0.57  % (12760)Memory used [KB]: 11129
% 1.62/0.57  % (12760)Time elapsed: 0.153 s
% 1.62/0.57  % (12760)------------------------------
% 1.62/0.57  % (12760)------------------------------
% 2.09/0.65  % (12772)Refutation not found, incomplete strategy% (12772)------------------------------
% 2.09/0.65  % (12772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.65  % (12772)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.65  
% 2.09/0.65  % (12772)Memory used [KB]: 1791
% 2.09/0.65  % (12772)Time elapsed: 0.215 s
% 2.09/0.65  % (12772)------------------------------
% 2.09/0.65  % (12772)------------------------------
% 2.09/0.65  % (12751)Refutation not found, incomplete strategy% (12751)------------------------------
% 2.09/0.65  % (12751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.65  % (12751)Termination reason: Refutation not found, incomplete strategy
% 2.09/0.65  
% 2.09/0.65  % (12751)Memory used [KB]: 6396
% 2.09/0.65  % (12751)Time elapsed: 0.191 s
% 2.09/0.65  % (12751)------------------------------
% 2.09/0.65  % (12751)------------------------------
% 2.09/0.66  % (12762)Refutation found. Thanks to Tanya!
% 2.09/0.66  % SZS status Theorem for theBenchmark
% 2.09/0.66  % SZS output start Proof for theBenchmark
% 2.09/0.66  fof(f1348,plain,(
% 2.09/0.66    $false),
% 2.09/0.66    inference(avatar_sat_refutation,[],[f99,f105,f309,f323,f335,f337,f339,f378,f400,f406,f408,f439,f465,f538,f563,f567,f703,f745,f794,f896,f990,f1000,f1002,f1004,f1047,f1121,f1223,f1239,f1343])).
% 2.09/0.66  fof(f1343,plain,(
% 2.09/0.66    ~spl7_23 | ~spl7_56),
% 2.09/0.66    inference(avatar_contradiction_clause,[],[f1341])).
% 2.09/0.66  fof(f1341,plain,(
% 2.09/0.66    $false | (~spl7_23 | ~spl7_56)),
% 2.09/0.66    inference(resolution,[],[f987,f562])).
% 2.09/0.66  fof(f562,plain,(
% 2.09/0.66    sP6(sK2,sK4,sK3,sK1,sK0) | ~spl7_23),
% 2.09/0.66    inference(avatar_component_clause,[],[f404])).
% 2.09/0.66  fof(f404,plain,(
% 2.09/0.66    spl7_23 <=> sP6(sK2,sK4,sK3,sK1,sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.09/0.66  fof(f987,plain,(
% 2.09/0.66    ( ! [X8] : (~sP6(sK2,X8,sK3,sK1,sK0)) ) | ~spl7_56),
% 2.09/0.66    inference(avatar_component_clause,[],[f986])).
% 2.09/0.66  fof(f986,plain,(
% 2.09/0.66    spl7_56 <=> ! [X8] : ~sP6(sK2,X8,sK3,sK1,sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).
% 2.09/0.66  fof(f1239,plain,(
% 2.09/0.66    ~spl7_52 | ~spl7_53 | ~spl7_54 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_51 | spl7_2),
% 2.09/0.66    inference(avatar_split_clause,[],[f1238,f97,f963,f301,f297,f293,f289,f975,f971,f967])).
% 2.09/0.66  fof(f967,plain,(
% 2.09/0.66    spl7_52 <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 2.09/0.66  fof(f971,plain,(
% 2.09/0.66    spl7_53 <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 2.09/0.66  fof(f975,plain,(
% 2.09/0.66    spl7_54 <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).
% 2.09/0.66  fof(f289,plain,(
% 2.09/0.66    spl7_8 <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4)))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 2.09/0.66  fof(f293,plain,(
% 2.09/0.66    spl7_9 <=> v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.09/0.66  fof(f297,plain,(
% 2.09/0.66    spl7_10 <=> v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 2.09/0.66  fof(f301,plain,(
% 2.09/0.66    spl7_11 <=> m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.09/0.66  fof(f963,plain,(
% 2.09/0.66    spl7_51 <=> v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3)))),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 2.09/0.66  fof(f97,plain,(
% 2.09/0.66    spl7_2 <=> sP5(sK4,sK3,sK2,sK1,sK0)),
% 2.09/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.09/0.66  fof(f1238,plain,(
% 2.09/0.66    ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_2),
% 2.09/0.66    inference(forward_demodulation,[],[f1237,f172])).
% 2.09/0.66  fof(f172,plain,(
% 2.09/0.66    k2_tmap_1(sK0,sK1,sK2,sK3) = k7_relat_1(sK2,u1_struct_0(sK3))),
% 2.09/0.66    inference(resolution,[],[f167,f54])).
% 2.09/0.66  fof(f54,plain,(
% 2.09/0.66    m1_pre_topc(sK3,sK0)),
% 2.09/0.66    inference(cnf_transformation,[],[f17])).
% 2.09/0.66  fof(f17,plain,(
% 2.09/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.09/0.66    inference(flattening,[],[f16])).
% 2.09/0.66  fof(f16,plain,(
% 2.09/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.09/0.66    inference(ennf_transformation,[],[f13])).
% 2.42/0.67  fof(f13,negated_conjecture,(
% 2.42/0.67    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.42/0.67    inference(negated_conjecture,[],[f12])).
% 2.42/0.67  fof(f12,conjecture,(
% 2.42/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).
% 2.42/0.67  fof(f167,plain,(
% 2.42/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0))) )),
% 2.42/0.67    inference(global_subsumption,[],[f55,f58,f59,f60,f61,f62,f63,f56,f166])).
% 2.42/0.67  fof(f166,plain,(
% 2.42/0.67    ( ! [X0] : (k2_tmap_1(sK0,sK1,sK2,X0) = k7_relat_1(sK2,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 2.42/0.67    inference(forward_demodulation,[],[f155,f130])).
% 2.42/0.67  fof(f130,plain,(
% 2.42/0.67    ( ! [X0] : (k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0)) )),
% 2.42/0.67    inference(global_subsumption,[],[f55,f127])).
% 2.42/0.67  fof(f127,plain,(
% 2.42/0.67    ( ! [X0] : (~v1_funct_1(sK2) | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k7_relat_1(sK2,X0)) )),
% 2.42/0.67    inference(resolution,[],[f91,f57])).
% 2.42/0.67  fof(f57,plain,(
% 2.42/0.67    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f91,plain,(
% 2.42/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f34])).
% 2.42/0.67  fof(f34,plain,(
% 2.42/0.67    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.42/0.67    inference(flattening,[],[f33])).
% 2.42/0.67  fof(f33,plain,(
% 2.42/0.67    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.42/0.67    inference(ennf_transformation,[],[f5])).
% 2.42/0.67  fof(f5,axiom,(
% 2.42/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.42/0.67  fof(f155,plain,(
% 2.42/0.67    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | k2_tmap_1(sK0,sK1,sK2,X0) = k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,u1_struct_0(X0))) )),
% 2.42/0.67    inference(resolution,[],[f80,f57])).
% 2.42/0.67  fof(f80,plain,(
% 2.42/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))) )),
% 2.42/0.67    inference(cnf_transformation,[],[f23])).
% 2.42/0.67  fof(f23,plain,(
% 2.42/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.42/0.67    inference(flattening,[],[f22])).
% 2.42/0.67  fof(f22,plain,(
% 2.42/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.42/0.67    inference(ennf_transformation,[],[f8])).
% 2.42/0.67  fof(f8,axiom,(
% 2.42/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 2.42/0.67  fof(f56,plain,(
% 2.42/0.67    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f63,plain,(
% 2.42/0.67    l1_pre_topc(sK0)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f62,plain,(
% 2.42/0.67    v2_pre_topc(sK0)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f61,plain,(
% 2.42/0.67    ~v2_struct_0(sK0)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f60,plain,(
% 2.42/0.67    l1_pre_topc(sK1)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f59,plain,(
% 2.42/0.67    v2_pre_topc(sK1)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f58,plain,(
% 2.42/0.67    ~v2_struct_0(sK1)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f55,plain,(
% 2.42/0.67    v1_funct_1(sK2)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f1237,plain,(
% 2.42/0.67    ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.42/0.67    inference(forward_demodulation,[],[f1236,f171])).
% 2.42/0.67  fof(f171,plain,(
% 2.42/0.67    k2_tmap_1(sK0,sK1,sK2,sK4) = k7_relat_1(sK2,u1_struct_0(sK4))),
% 2.42/0.67    inference(resolution,[],[f167,f50])).
% 2.42/0.67  fof(f50,plain,(
% 2.42/0.67    m1_pre_topc(sK4,sK0)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f1236,plain,(
% 2.42/0.67    ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.42/0.67    inference(forward_demodulation,[],[f1235,f171])).
% 2.42/0.67  fof(f1235,plain,(
% 2.42/0.67    ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.42/0.67    inference(forward_demodulation,[],[f1234,f171])).
% 2.42/0.67  fof(f1234,plain,(
% 2.42/0.67    ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.42/0.67    inference(forward_demodulation,[],[f1233,f171])).
% 2.42/0.67  fof(f1233,plain,(
% 2.42/0.67    ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.42/0.67    inference(forward_demodulation,[],[f1232,f172])).
% 2.42/0.67  fof(f1232,plain,(
% 2.42/0.67    ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.42/0.67    inference(forward_demodulation,[],[f1231,f172])).
% 2.42/0.67  fof(f1231,plain,(
% 2.42/0.67    ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.42/0.67    inference(forward_demodulation,[],[f1230,f172])).
% 2.42/0.67  fof(f1230,plain,(
% 2.42/0.67    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_2),
% 2.42/0.67    inference(resolution,[],[f104,f35])).
% 2.42/0.67  fof(f35,plain,(
% 2.42/0.67    ( ! [X4,X2,X0,X3,X1] : (sP5(X4,X3,X2,X1,X0) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) )),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f104,plain,(
% 2.42/0.67    ~sP5(sK4,sK3,sK2,sK1,sK0) | spl7_2),
% 2.42/0.67    inference(avatar_component_clause,[],[f97])).
% 2.42/0.67  fof(f1223,plain,(
% 2.42/0.67    spl7_45 | ~spl7_54),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f1222])).
% 2.42/0.67  fof(f1222,plain,(
% 2.42/0.67    $false | (spl7_45 | ~spl7_54)),
% 2.42/0.67    inference(resolution,[],[f1199,f976])).
% 2.42/0.67  fof(f976,plain,(
% 2.42/0.67    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~spl7_54),
% 2.42/0.67    inference(avatar_component_clause,[],[f975])).
% 2.42/0.67  fof(f1199,plain,(
% 2.42/0.67    ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl7_45),
% 2.42/0.67    inference(forward_demodulation,[],[f699,f172])).
% 2.42/0.67  fof(f699,plain,(
% 2.42/0.67    ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | spl7_45),
% 2.42/0.67    inference(avatar_component_clause,[],[f698])).
% 2.42/0.67  fof(f698,plain,(
% 2.42/0.67    spl7_45 <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.42/0.67  fof(f1121,plain,(
% 2.42/0.67    spl7_42 | ~spl7_52),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f1120])).
% 2.42/0.67  fof(f1120,plain,(
% 2.42/0.67    $false | (spl7_42 | ~spl7_52)),
% 2.42/0.67    inference(resolution,[],[f968,f1028])).
% 2.42/0.67  fof(f1028,plain,(
% 2.42/0.67    ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_42),
% 2.42/0.67    inference(forward_demodulation,[],[f620,f172])).
% 2.42/0.67  fof(f620,plain,(
% 2.42/0.67    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | spl7_42),
% 2.42/0.67    inference(avatar_component_clause,[],[f619])).
% 2.42/0.67  fof(f619,plain,(
% 2.42/0.67    spl7_42 <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 2.42/0.67  fof(f968,plain,(
% 2.42/0.67    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~spl7_52),
% 2.42/0.67    inference(avatar_component_clause,[],[f967])).
% 2.42/0.67  fof(f1047,plain,(
% 2.42/0.67    ~spl7_2 | spl7_46),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f1046])).
% 2.42/0.67  fof(f1046,plain,(
% 2.42/0.67    $false | (~spl7_2 | spl7_46)),
% 2.42/0.67    inference(resolution,[],[f922,f98])).
% 2.42/0.67  fof(f98,plain,(
% 2.42/0.67    sP5(sK4,sK3,sK2,sK1,sK0) | ~spl7_2),
% 2.42/0.67    inference(avatar_component_clause,[],[f97])).
% 2.42/0.67  fof(f922,plain,(
% 2.42/0.67    ( ! [X3] : (~sP5(X3,sK3,sK2,sK1,sK0)) ) | spl7_46),
% 2.42/0.67    inference(resolution,[],[f702,f38])).
% 2.42/0.67  fof(f38,plain,(
% 2.42/0.67    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~sP5(X4,X3,X2,X1,X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f702,plain,(
% 2.42/0.67    ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | spl7_46),
% 2.42/0.67    inference(avatar_component_clause,[],[f701])).
% 2.42/0.67  fof(f701,plain,(
% 2.42/0.67    spl7_46 <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 2.42/0.67  fof(f1004,plain,(
% 2.42/0.67    ~spl7_15 | ~spl7_47 | ~spl7_17 | spl7_54),
% 2.42/0.67    inference(avatar_split_clause,[],[f1003,f975,f333,f743,f327])).
% 2.42/0.67  fof(f327,plain,(
% 2.42/0.67    spl7_15 <=> l1_struct_0(sK0)),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 2.42/0.67  fof(f743,plain,(
% 2.42/0.67    spl7_47 <=> l1_struct_0(sK3)),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 2.42/0.67  fof(f333,plain,(
% 2.42/0.67    spl7_17 <=> l1_struct_0(sK1)),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.42/0.67  fof(f1003,plain,(
% 2.42/0.67    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.42/0.67    inference(global_subsumption,[],[f55,f56,f57,f942])).
% 2.42/0.67  fof(f942,plain,(
% 2.42/0.67    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.42/0.67    inference(superposition,[],[f90,f172])).
% 2.42/0.67  fof(f90,plain,(
% 2.42/0.67    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f32])).
% 2.42/0.67  fof(f32,plain,(
% 2.42/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 2.42/0.67    inference(flattening,[],[f31])).
% 2.42/0.67  fof(f31,plain,(
% 2.42/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 2.42/0.67    inference(ennf_transformation,[],[f10])).
% 2.42/0.67  fof(f10,axiom,(
% 2.42/0.67    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 2.42/0.67  fof(f1002,plain,(
% 2.42/0.67    ~spl7_15 | ~spl7_47 | ~spl7_17 | spl7_52),
% 2.42/0.67    inference(avatar_split_clause,[],[f1001,f967,f333,f743,f327])).
% 2.42/0.67  fof(f1001,plain,(
% 2.42/0.67    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.42/0.67    inference(global_subsumption,[],[f55,f56,f57,f941])).
% 2.42/0.67  fof(f941,plain,(
% 2.42/0.67    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK3)),u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.42/0.67    inference(superposition,[],[f89,f172])).
% 2.42/0.67  fof(f89,plain,(
% 2.42/0.67    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f32])).
% 2.42/0.67  fof(f1000,plain,(
% 2.42/0.67    ~spl7_15 | ~spl7_47 | ~spl7_17 | spl7_51),
% 2.42/0.67    inference(avatar_split_clause,[],[f999,f963,f333,f743,f327])).
% 2.42/0.67  fof(f999,plain,(
% 2.42/0.67    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.42/0.67    inference(global_subsumption,[],[f55,f56,f57,f940])).
% 2.42/0.67  fof(f940,plain,(
% 2.42/0.67    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK3))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0)),
% 2.42/0.67    inference(superposition,[],[f88,f172])).
% 2.42/0.67  fof(f88,plain,(
% 2.42/0.67    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~l1_struct_0(X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f32])).
% 2.42/0.67  fof(f990,plain,(
% 2.42/0.67    spl7_56 | spl7_53),
% 2.42/0.67    inference(avatar_split_clause,[],[f934,f971,f986])).
% 2.42/0.67  fof(f934,plain,(
% 2.42/0.67    ( ! [X10] : (v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK3)),sK3,sK1) | ~sP6(sK2,X10,sK3,sK1,sK0)) )),
% 2.42/0.67    inference(superposition,[],[f69,f172])).
% 2.42/0.67  fof(f69,plain,(
% 2.42/0.67    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~sP6(X4,X3,X2,X1,X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f21])).
% 2.42/0.67  fof(f21,plain,(
% 2.42/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.42/0.67    inference(flattening,[],[f20])).
% 2.42/0.67  fof(f20,plain,(
% 2.42/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.42/0.67    inference(ennf_transformation,[],[f11])).
% 2.42/0.67  fof(f11,axiom,(
% 2.42/0.67    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).
% 2.42/0.67  fof(f896,plain,(
% 2.42/0.67    spl7_27),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f895])).
% 2.42/0.67  fof(f895,plain,(
% 2.42/0.67    $false | spl7_27),
% 2.42/0.67    inference(resolution,[],[f453,f57])).
% 2.42/0.67  fof(f453,plain,(
% 2.42/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl7_27),
% 2.42/0.67    inference(avatar_component_clause,[],[f452])).
% 2.42/0.67  fof(f452,plain,(
% 2.42/0.67    spl7_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 2.42/0.67  fof(f794,plain,(
% 2.42/0.67    spl7_47),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f793])).
% 2.42/0.67  fof(f793,plain,(
% 2.42/0.67    $false | spl7_47),
% 2.42/0.67    inference(resolution,[],[f769,f109])).
% 2.42/0.67  fof(f109,plain,(
% 2.42/0.67    l1_pre_topc(sK3)),
% 2.42/0.67    inference(global_subsumption,[],[f63,f107])).
% 2.42/0.67  fof(f107,plain,(
% 2.42/0.67    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 2.42/0.67    inference(resolution,[],[f65,f54])).
% 2.42/0.67  fof(f65,plain,(
% 2.42/0.67    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f19])).
% 2.42/0.67  fof(f19,plain,(
% 2.42/0.67    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.42/0.67    inference(ennf_transformation,[],[f7])).
% 2.42/0.67  fof(f7,axiom,(
% 2.42/0.67    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.42/0.67  fof(f769,plain,(
% 2.42/0.67    ~l1_pre_topc(sK3) | spl7_47),
% 2.42/0.67    inference(resolution,[],[f744,f64])).
% 2.42/0.67  fof(f64,plain,(
% 2.42/0.67    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f18])).
% 2.42/0.67  fof(f18,plain,(
% 2.42/0.67    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.42/0.67    inference(ennf_transformation,[],[f6])).
% 2.42/0.67  fof(f6,axiom,(
% 2.42/0.67    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.42/0.67  fof(f744,plain,(
% 2.42/0.67    ~l1_struct_0(sK3) | spl7_47),
% 2.42/0.67    inference(avatar_component_clause,[],[f743])).
% 2.42/0.67  fof(f745,plain,(
% 2.42/0.67    ~spl7_15 | ~spl7_47 | ~spl7_27 | ~spl7_26 | ~spl7_25 | ~spl7_17 | spl7_33),
% 2.42/0.67    inference(avatar_split_clause,[],[f737,f584,f333,f446,f449,f452,f743,f327])).
% 2.42/0.67  fof(f449,plain,(
% 2.42/0.67    spl7_26 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 2.42/0.67  fof(f446,plain,(
% 2.42/0.67    spl7_25 <=> v1_funct_1(sK2)),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 2.42/0.67  fof(f584,plain,(
% 2.42/0.67    spl7_33 <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 2.42/0.67  fof(f737,plain,(
% 2.42/0.67    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK0) | spl7_33),
% 2.42/0.67    inference(resolution,[],[f585,f88])).
% 2.42/0.67  fof(f585,plain,(
% 2.42/0.67    ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_33),
% 2.42/0.67    inference(avatar_component_clause,[],[f584])).
% 2.42/0.67  fof(f703,plain,(
% 2.42/0.67    ~spl7_33 | ~spl7_45 | ~spl7_46 | ~spl7_42 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | spl7_23),
% 2.42/0.67    inference(avatar_split_clause,[],[f696,f404,f301,f297,f293,f289,f619,f701,f698,f584])).
% 2.42/0.67  fof(f696,plain,(
% 2.42/0.67    ~m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_23),
% 2.42/0.67    inference(forward_demodulation,[],[f695,f171])).
% 2.42/0.67  fof(f695,plain,(
% 2.42/0.67    ~v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_23),
% 2.42/0.67    inference(forward_demodulation,[],[f694,f171])).
% 2.42/0.67  fof(f694,plain,(
% 2.42/0.67    ~v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_23),
% 2.42/0.67    inference(forward_demodulation,[],[f693,f171])).
% 2.42/0.67  fof(f693,plain,(
% 2.42/0.67    ~v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_23),
% 2.42/0.67    inference(forward_demodulation,[],[f692,f171])).
% 2.42/0.67  fof(f692,plain,(
% 2.42/0.67    ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) | ~v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) | ~v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) | ~m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) | spl7_23),
% 2.42/0.67    inference(resolution,[],[f405,f66])).
% 2.42/0.67  fof(f66,plain,(
% 2.42/0.67    ( ! [X4,X2,X0,X3,X1] : (sP6(X4,X3,X2,X1,X0) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) )),
% 2.42/0.67    inference(cnf_transformation,[],[f21])).
% 2.42/0.67  fof(f405,plain,(
% 2.42/0.67    ~sP6(sK2,sK4,sK3,sK1,sK0) | spl7_23),
% 2.42/0.67    inference(avatar_component_clause,[],[f404])).
% 2.42/0.67  fof(f567,plain,(
% 2.42/0.67    ~spl7_14 | ~spl7_23),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f564])).
% 2.42/0.67  fof(f564,plain,(
% 2.42/0.67    $false | (~spl7_14 | ~spl7_23)),
% 2.42/0.67    inference(resolution,[],[f562,f320])).
% 2.42/0.67  fof(f320,plain,(
% 2.42/0.67    ( ! [X12] : (~sP6(sK2,sK4,X12,sK1,sK0)) ) | ~spl7_14),
% 2.42/0.67    inference(avatar_component_clause,[],[f319])).
% 2.42/0.67  fof(f319,plain,(
% 2.42/0.67    spl7_14 <=> ! [X12] : ~sP6(sK2,sK4,X12,sK1,sK0)),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 2.42/0.67  fof(f563,plain,(
% 2.42/0.67    ~spl7_1 | spl7_23),
% 2.42/0.67    inference(avatar_split_clause,[],[f561,f404,f94])).
% 2.42/0.67  fof(f94,plain,(
% 2.42/0.67    spl7_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.42/0.67  fof(f561,plain,(
% 2.42/0.67    sP6(sK2,sK4,sK3,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.42/0.67    inference(global_subsumption,[],[f55,f58,f59,f60,f56,f57,f554])).
% 2.42/0.67  fof(f554,plain,(
% 2.42/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | sP6(sK2,sK4,sK3,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.42/0.67    inference(duplicate_literal_removal,[],[f553])).
% 2.42/0.67  fof(f553,plain,(
% 2.42/0.67    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | sP6(sK2,sK4,sK3,sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.42/0.67    inference(superposition,[],[f257,f175])).
% 2.42/0.67  fof(f175,plain,(
% 2.42/0.67    sK2 = k2_tmap_1(sK0,sK1,sK2,sK0)),
% 2.42/0.67    inference(forward_demodulation,[],[f173,f123])).
% 2.42/0.67  fof(f123,plain,(
% 2.42/0.67    sK2 = k7_relat_1(sK2,u1_struct_0(sK0))),
% 2.42/0.67    inference(global_subsumption,[],[f110,f120])).
% 2.42/0.67  fof(f120,plain,(
% 2.42/0.67    sK2 = k7_relat_1(sK2,u1_struct_0(sK0)) | ~v1_relat_1(sK2)),
% 2.42/0.67    inference(resolution,[],[f119,f115])).
% 2.42/0.67  fof(f115,plain,(
% 2.42/0.67    v4_relat_1(sK2,u1_struct_0(sK0))),
% 2.42/0.67    inference(resolution,[],[f85,f57])).
% 2.42/0.67  fof(f85,plain,(
% 2.42/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f28])).
% 2.42/0.67  fof(f28,plain,(
% 2.42/0.67    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.67    inference(ennf_transformation,[],[f15])).
% 2.42/0.67  fof(f15,plain,(
% 2.42/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.42/0.67    inference(pure_predicate_removal,[],[f4])).
% 2.42/0.67  fof(f4,axiom,(
% 2.42/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.42/0.67  fof(f119,plain,(
% 2.42/0.67    ( ! [X0,X1] : (~v4_relat_1(X0,X1) | k7_relat_1(X0,X1) = X0 | ~v1_relat_1(X0)) )),
% 2.42/0.67    inference(duplicate_literal_removal,[],[f118])).
% 2.42/0.67  fof(f118,plain,(
% 2.42/0.67    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 2.42/0.67    inference(resolution,[],[f81,f83])).
% 2.42/0.67  fof(f83,plain,(
% 2.42/0.67    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f26])).
% 2.42/0.67  fof(f26,plain,(
% 2.42/0.67    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.42/0.67    inference(ennf_transformation,[],[f1])).
% 2.42/0.67  fof(f1,axiom,(
% 2.42/0.67    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.42/0.67  fof(f81,plain,(
% 2.42/0.67    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 2.42/0.67    inference(cnf_transformation,[],[f25])).
% 2.42/0.67  fof(f25,plain,(
% 2.42/0.67    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.42/0.67    inference(flattening,[],[f24])).
% 2.42/0.67  fof(f24,plain,(
% 2.42/0.67    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.42/0.67    inference(ennf_transformation,[],[f2])).
% 2.42/0.67  fof(f2,axiom,(
% 2.42/0.67    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 2.42/0.67  fof(f110,plain,(
% 2.42/0.67    v1_relat_1(sK2)),
% 2.42/0.67    inference(resolution,[],[f84,f57])).
% 2.42/0.67  fof(f84,plain,(
% 2.42/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f27])).
% 2.42/0.67  fof(f27,plain,(
% 2.42/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.42/0.67    inference(ennf_transformation,[],[f3])).
% 2.42/0.67  fof(f3,axiom,(
% 2.42/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.42/0.67  fof(f173,plain,(
% 2.42/0.67    k7_relat_1(sK2,u1_struct_0(sK0)) = k2_tmap_1(sK0,sK1,sK2,sK0)),
% 2.42/0.67    inference(resolution,[],[f167,f144])).
% 2.42/0.67  fof(f144,plain,(
% 2.42/0.67    m1_pre_topc(sK0,sK0)),
% 2.42/0.67    inference(global_subsumption,[],[f49,f53,f61,f63,f50,f54,f142])).
% 2.42/0.67  fof(f142,plain,(
% 2.42/0.67    m1_pre_topc(sK0,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK0)),
% 2.42/0.67    inference(superposition,[],[f87,f51])).
% 2.42/0.67  fof(f51,plain,(
% 2.42/0.67    sK0 = k1_tsep_1(sK0,sK3,sK4)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f87,plain,(
% 2.42/0.67    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f30])).
% 2.42/0.67  fof(f30,plain,(
% 2.42/0.67    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.42/0.67    inference(flattening,[],[f29])).
% 2.42/0.67  fof(f29,plain,(
% 2.42/0.67    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.42/0.67    inference(ennf_transformation,[],[f14])).
% 2.42/0.67  fof(f14,plain,(
% 2.42/0.67    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.42/0.67    inference(pure_predicate_removal,[],[f9])).
% 2.42/0.67  fof(f9,axiom,(
% 2.42/0.67    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.42/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 2.42/0.67  fof(f53,plain,(
% 2.42/0.67    ~v2_struct_0(sK3)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f49,plain,(
% 2.42/0.67    ~v2_struct_0(sK4)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f257,plain,(
% 2.42/0.67    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | sP6(X1,sK4,sK3,X0,sK0) | ~v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0)) | ~v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0)) )),
% 2.42/0.67    inference(global_subsumption,[],[f49,f53,f61,f62,f63,f50,f54,f52,f254])).
% 2.42/0.67  fof(f254,plain,(
% 2.42/0.67    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK0,X0,X1,sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | sP6(X1,sK4,sK3,X0,sK0) | ~v1_funct_1(k2_tmap_1(sK0,X0,X1,sK0)) | ~v1_funct_2(k2_tmap_1(sK0,X0,X1,sK0),u1_struct_0(sK0),u1_struct_0(X0)) | ~v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | v2_struct_0(sK0)) )),
% 2.42/0.67    inference(superposition,[],[f75,f51])).
% 2.42/0.67  fof(f75,plain,(
% 2.42/0.67    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | sP6(X4,X3,X2,X1,X0) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | v2_struct_0(X0)) )),
% 2.42/0.67    inference(cnf_transformation,[],[f21])).
% 2.42/0.67  fof(f52,plain,(
% 2.42/0.67    r4_tsep_1(sK0,sK3,sK4)),
% 2.42/0.67    inference(cnf_transformation,[],[f17])).
% 2.42/0.67  fof(f538,plain,(
% 2.42/0.67    spl7_26),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f537])).
% 2.42/0.67  fof(f537,plain,(
% 2.42/0.67    $false | spl7_26),
% 2.42/0.67    inference(resolution,[],[f450,f56])).
% 2.42/0.67  fof(f450,plain,(
% 2.42/0.67    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | spl7_26),
% 2.42/0.67    inference(avatar_component_clause,[],[f449])).
% 2.42/0.67  fof(f465,plain,(
% 2.42/0.67    spl7_25),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f464])).
% 2.42/0.67  fof(f464,plain,(
% 2.42/0.67    $false | spl7_25),
% 2.42/0.67    inference(resolution,[],[f447,f55])).
% 2.42/0.67  fof(f447,plain,(
% 2.42/0.67    ~v1_funct_1(sK2) | spl7_25),
% 2.42/0.67    inference(avatar_component_clause,[],[f446])).
% 2.42/0.67  fof(f439,plain,(
% 2.42/0.67    ~spl7_2 | ~spl7_12),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f437])).
% 2.42/0.67  fof(f437,plain,(
% 2.42/0.67    $false | (~spl7_2 | ~spl7_12)),
% 2.42/0.67    inference(resolution,[],[f306,f98])).
% 2.42/0.67  fof(f306,plain,(
% 2.42/0.67    ( ! [X4] : (~sP5(sK4,X4,sK2,sK1,sK0)) ) | ~spl7_12),
% 2.42/0.67    inference(avatar_component_clause,[],[f305])).
% 2.42/0.67  fof(f305,plain,(
% 2.42/0.67    spl7_12 <=> ! [X4] : ~sP5(sK4,X4,sK2,sK1,sK0)),
% 2.42/0.67    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.42/0.67  fof(f408,plain,(
% 2.42/0.67    spl7_17),
% 2.42/0.67    inference(avatar_contradiction_clause,[],[f407])).
% 2.42/0.67  fof(f407,plain,(
% 2.42/0.67    $false | spl7_17),
% 2.42/0.67    inference(resolution,[],[f369,f60])).
% 2.42/0.67  fof(f369,plain,(
% 2.42/0.67    ~l1_pre_topc(sK1) | spl7_17),
% 2.42/0.67    inference(resolution,[],[f334,f64])).
% 2.42/0.67  fof(f334,plain,(
% 2.42/0.67    ~l1_struct_0(sK1) | spl7_17),
% 2.42/0.67    inference(avatar_component_clause,[],[f333])).
% 2.42/0.67  fof(f406,plain,(
% 2.42/0.67    ~spl7_23 | spl7_1),
% 2.42/0.67    inference(avatar_split_clause,[],[f402,f94,f404])).
% 2.42/0.67  fof(f402,plain,(
% 2.42/0.67    v5_pre_topc(sK2,sK0,sK1) | ~sP6(sK2,sK4,sK3,sK1,sK0)),
% 2.42/0.67    inference(global_subsumption,[],[f55,f58,f59,f60,f56,f57,f401])).
% 2.42/0.67  fof(f401,plain,(
% 2.42/0.67    v5_pre_topc(sK2,sK0,sK1) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~sP6(sK2,sK4,sK3,sK1,sK0)),
% 2.42/0.67    inference(superposition,[],[f224,f175])).
% 2.42/0.68  fof(f224,plain,(
% 2.42/0.68    ( ! [X0,X1] : (v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~sP6(X1,sK4,sK3,X0,sK0)) )),
% 2.42/0.68    inference(global_subsumption,[],[f49,f53,f61,f62,f63,f50,f54,f52,f223])).
% 2.42/0.68  fof(f223,plain,(
% 2.42/0.68    ( ! [X0,X1] : (v5_pre_topc(k2_tmap_1(sK0,X0,X1,sK0),sK0,X0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | ~r4_tsep_1(sK0,sK3,sK4) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~sP6(X1,sK4,sK3,X0,sK0) | v2_struct_0(sK0)) )),
% 2.42/0.68    inference(superposition,[],[f78,f51])).
% 2.42/0.68  fof(f78,plain,(
% 2.42/0.68    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | ~r4_tsep_1(X0,X2,X3) | ~v1_funct_1(X4) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~sP6(X4,X3,X2,X1,X0) | v2_struct_0(X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f21])).
% 2.42/0.68  fof(f400,plain,(
% 2.42/0.68    spl7_16),
% 2.42/0.68    inference(avatar_contradiction_clause,[],[f399])).
% 2.42/0.68  fof(f399,plain,(
% 2.42/0.68    $false | spl7_16),
% 2.42/0.68    inference(resolution,[],[f361,f108])).
% 2.42/0.68  fof(f108,plain,(
% 2.42/0.68    l1_pre_topc(sK4)),
% 2.42/0.68    inference(global_subsumption,[],[f63,f106])).
% 2.42/0.68  fof(f106,plain,(
% 2.42/0.68    ~l1_pre_topc(sK0) | l1_pre_topc(sK4)),
% 2.42/0.68    inference(resolution,[],[f65,f50])).
% 2.42/0.68  fof(f361,plain,(
% 2.42/0.68    ~l1_pre_topc(sK4) | spl7_16),
% 2.42/0.68    inference(resolution,[],[f331,f64])).
% 2.42/0.68  fof(f331,plain,(
% 2.42/0.68    ~l1_struct_0(sK4) | spl7_16),
% 2.42/0.68    inference(avatar_component_clause,[],[f330])).
% 2.42/0.68  fof(f330,plain,(
% 2.42/0.68    spl7_16 <=> l1_struct_0(sK4)),
% 2.42/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 2.42/0.68  fof(f378,plain,(
% 2.42/0.68    spl7_15),
% 2.42/0.68    inference(avatar_contradiction_clause,[],[f377])).
% 2.42/0.68  fof(f377,plain,(
% 2.42/0.68    $false | spl7_15),
% 2.42/0.68    inference(resolution,[],[f356,f63])).
% 2.42/0.68  fof(f356,plain,(
% 2.42/0.68    ~l1_pre_topc(sK0) | spl7_15),
% 2.42/0.68    inference(resolution,[],[f328,f64])).
% 2.42/0.68  fof(f328,plain,(
% 2.42/0.68    ~l1_struct_0(sK0) | spl7_15),
% 2.42/0.68    inference(avatar_component_clause,[],[f327])).
% 2.42/0.68  fof(f339,plain,(
% 2.42/0.68    ~spl7_15 | ~spl7_16 | ~spl7_17 | spl7_11),
% 2.42/0.68    inference(avatar_split_clause,[],[f338,f301,f333,f330,f327])).
% 2.42/0.68  fof(f338,plain,(
% 2.42/0.68    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.42/0.68    inference(global_subsumption,[],[f55,f56,f57,f278])).
% 2.42/0.68  fof(f278,plain,(
% 2.42/0.68    m1_subset_1(k7_relat_1(sK2,u1_struct_0(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.42/0.68    inference(superposition,[],[f90,f171])).
% 2.42/0.68  fof(f337,plain,(
% 2.42/0.68    ~spl7_15 | ~spl7_16 | ~spl7_17 | spl7_9),
% 2.42/0.68    inference(avatar_split_clause,[],[f336,f293,f333,f330,f327])).
% 2.42/0.68  fof(f336,plain,(
% 2.42/0.68    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.42/0.68    inference(global_subsumption,[],[f55,f56,f57,f277])).
% 2.42/0.68  fof(f277,plain,(
% 2.42/0.68    v1_funct_2(k7_relat_1(sK2,u1_struct_0(sK4)),u1_struct_0(sK4),u1_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.42/0.68    inference(superposition,[],[f89,f171])).
% 2.42/0.68  fof(f335,plain,(
% 2.42/0.68    ~spl7_15 | ~spl7_16 | ~spl7_17 | spl7_8),
% 2.42/0.68    inference(avatar_split_clause,[],[f325,f289,f333,f330,f327])).
% 2.42/0.68  fof(f325,plain,(
% 2.42/0.68    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~l1_struct_0(sK1) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.42/0.68    inference(global_subsumption,[],[f55,f56,f57,f276])).
% 2.42/0.68  fof(f276,plain,(
% 2.42/0.68    v1_funct_1(k7_relat_1(sK2,u1_struct_0(sK4))) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK4) | ~l1_struct_0(sK0)),
% 2.42/0.68    inference(superposition,[],[f88,f171])).
% 2.42/0.68  fof(f323,plain,(
% 2.42/0.68    spl7_14 | spl7_10),
% 2.42/0.68    inference(avatar_split_clause,[],[f274,f297,f319])).
% 2.42/0.68  fof(f274,plain,(
% 2.42/0.68    ( ! [X14] : (v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~sP6(sK2,sK4,X14,sK1,sK0)) )),
% 2.42/0.68    inference(superposition,[],[f73,f171])).
% 2.42/0.68  fof(f73,plain,(
% 2.42/0.68    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~sP6(X4,X3,X2,X1,X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f21])).
% 2.42/0.68  fof(f309,plain,(
% 2.42/0.68    spl7_12 | spl7_10),
% 2.42/0.68    inference(avatar_split_clause,[],[f266,f297,f305])).
% 2.42/0.68  fof(f266,plain,(
% 2.42/0.68    ( ! [X6] : (v5_pre_topc(k7_relat_1(sK2,u1_struct_0(sK4)),sK4,sK1) | ~sP5(sK4,X6,sK2,sK1,sK0)) )),
% 2.42/0.68    inference(superposition,[],[f42,f171])).
% 2.42/0.68  fof(f42,plain,(
% 2.42/0.68    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~sP5(X4,X3,X2,X1,X0)) )),
% 2.42/0.68    inference(cnf_transformation,[],[f17])).
% 2.42/0.68  fof(f105,plain,(
% 2.42/0.68    ~spl7_1 | ~spl7_2),
% 2.42/0.68    inference(avatar_split_clause,[],[f102,f97,f94])).
% 2.42/0.68  fof(f102,plain,(
% 2.42/0.68    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v5_pre_topc(sK2,sK0,sK1)),
% 2.42/0.68    inference(global_subsumption,[],[f92,f100,f101,f44])).
% 2.42/0.68  fof(f44,plain,(
% 2.42/0.68    ~sP5(sK4,sK3,sK2,sK1,sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.42/0.68    inference(cnf_transformation,[],[f17])).
% 2.42/0.68  fof(f101,plain,(
% 2.42/0.68    v1_funct_1(sK2)),
% 2.42/0.68    inference(global_subsumption,[],[f55])).
% 2.42/0.68  fof(f100,plain,(
% 2.42/0.68    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.42/0.68    inference(global_subsumption,[],[f56])).
% 2.42/0.68  fof(f92,plain,(
% 2.42/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.42/0.68    inference(global_subsumption,[],[f57])).
% 2.42/0.68  fof(f99,plain,(
% 2.42/0.68    spl7_1 | spl7_2),
% 2.42/0.68    inference(avatar_split_clause,[],[f47,f97,f94])).
% 2.42/0.68  fof(f47,plain,(
% 2.42/0.68    sP5(sK4,sK3,sK2,sK1,sK0) | v5_pre_topc(sK2,sK0,sK1)),
% 2.42/0.68    inference(cnf_transformation,[],[f17])).
% 2.42/0.68  % SZS output end Proof for theBenchmark
% 2.42/0.68  % (12762)------------------------------
% 2.42/0.68  % (12762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.68  % (12762)Termination reason: Refutation
% 2.42/0.68  
% 2.42/0.68  % (12762)Memory used [KB]: 12920
% 2.42/0.68  % (12762)Time elapsed: 0.248 s
% 2.42/0.68  % (12762)------------------------------
% 2.42/0.68  % (12762)------------------------------
% 2.42/0.68  % (12749)Success in time 0.316 s
%------------------------------------------------------------------------------
