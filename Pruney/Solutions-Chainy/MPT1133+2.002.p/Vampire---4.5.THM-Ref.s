%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:26 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  134 (1291 expanded)
%              Number of leaves         :   19 ( 297 expanded)
%              Depth                    :   17
%              Number of atoms          :  440 (7838 expanded)
%              Number of equality atoms :   21 ( 636 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f378,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f130,f145,f157,f203,f213,f274,f317,f345,f363,f367,f371,f377])).

fof(f377,plain,
    ( spl5_1
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl5_1
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f276,f280,f285,f362])).

fof(f362,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl5_20
  <=> ! [X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f285,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_1
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f70,f278,f238])).

fof(f238,plain,
    ( ! [X1] :
        ( v4_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl5_10 ),
    inference(backward_demodulation,[],[f212,f219])).

fof(f219,plain,(
    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f90,f89,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f89,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(unit_resulting_resolution,[],[f82,f83,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f83,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f68,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f34,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f82,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    inference(unit_resulting_resolution,[],[f83,f46])).

fof(f212,plain,
    ( ! [X1] :
        ( v4_pre_topc(X1,sK0)
        | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl5_10
  <=> ! [X1] :
        ( ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v4_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f278,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f28,f32,f34,f29,f30,f121,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f121,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f280,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f31,f32,f277,f276,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

% (31705)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f277,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f28,f34,f32,f29,f30,f121,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v4_pre_topc(sK4(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f276,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f28,f34,f32,f29,f30,f121,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f371,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f30,f359])).

fof(f359,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl5_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f367,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f29,f355])).

fof(f355,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl5_18
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f363,plain,
    ( ~ spl5_14
    | ~ spl5_16
    | ~ spl5_18
    | ~ spl5_19
    | spl5_20
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f302,f123,f361,f357,f353,f332,f304])).

fof(f304,plain,
    ( spl5_14
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f332,plain,
    ( spl5_16
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f123,plain,
    ( spl5_2
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f302,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f301,f219])).

fof(f301,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f300,f170])).

fof(f170,plain,(
    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f80,f79,f39])).

fof(f79,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(unit_resulting_resolution,[],[f72,f73,f41])).

fof(f73,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f62,f49])).

fof(f62,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f32,f46])).

fof(f72,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f62,f48])).

fof(f80,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(unit_resulting_resolution,[],[f73,f46])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f299,f170])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f298,f219])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f297,f170])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f296,f219])).

fof(f296,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f293,f170])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_2 ),
    inference(resolution,[],[f55,f124])).

fof(f124,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(sK2,X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2,X2),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f345,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | spl5_16 ),
    inference(unit_resulting_resolution,[],[f68,f334,f49])).

fof(f334,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f332])).

fof(f317,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl5_14 ),
    inference(unit_resulting_resolution,[],[f62,f306,f49])).

fof(f306,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f304])).

fof(f274,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f34,f33,f208,f70,f237,f44])).

fof(f237,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_2 ),
    inference(backward_demodulation,[],[f189,f219])).

fof(f189,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_2 ),
    inference(backward_demodulation,[],[f133,f170])).

fof(f133,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f28,f73,f83,f51,f50,f125,f38])).

fof(f125,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f26,f27])).

fof(f27,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f25,f27])).

fof(f25,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f208,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ spl5_1
    | spl5_2
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f34,f32,f28,f120,f29,f30,f188,f204,f35])).

fof(f204,plain,
    ( v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | spl5_2
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f188,f132,f202])).

fof(f202,plain,
    ( ! [X1] :
        ( v4_pre_topc(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl5_9
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        | v4_pre_topc(X1,sK1)
        | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f132,plain,
    ( v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f28,f73,f83,f51,f50,f125,f37])).

fof(f188,plain,
    ( m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_2 ),
    inference(backward_demodulation,[],[f131,f170])).

fof(f131,plain,
    ( m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f28,f73,f83,f51,f50,f125,f36])).

fof(f120,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f213,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f65,f150,f211])).

fof(f150,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f65,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | v4_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f203,plain,
    ( ~ spl5_4
    | spl5_9 ),
    inference(avatar_split_clause,[],[f186,f201,f138])).

fof(f138,plain,
    ( spl5_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f186,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v4_pre_topc(X1,sK1) ) ),
    inference(backward_demodulation,[],[f59,f170])).

fof(f59,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | v4_pre_topc(X1,sK1) ) ),
    inference(resolution,[],[f31,f43])).

fof(f157,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f34,f152])).

fof(f152,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f145,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f32,f140])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f130,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f54,f123,f119])).

fof(f54,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f22,f27])).

fof(f22,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f126,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f53,f123,f119])).

fof(f53,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f23,f27])).

fof(f23,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:17:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (31691)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (31696)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (31708)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (31699)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (31708)Refutation not found, incomplete strategy% (31708)------------------------------
% 0.21/0.51  % (31708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31715)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (31701)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (31713)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (31712)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (31701)Refutation not found, incomplete strategy% (31701)------------------------------
% 0.21/0.52  % (31701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31704)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (31708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31708)Memory used [KB]: 10746
% 0.21/0.53  % (31708)Time elapsed: 0.111 s
% 0.21/0.53  % (31708)------------------------------
% 0.21/0.53  % (31708)------------------------------
% 0.21/0.53  % (31717)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (31695)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (31713)Refutation not found, incomplete strategy% (31713)------------------------------
% 0.21/0.53  % (31713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31710)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (31701)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31701)Memory used [KB]: 10746
% 0.21/0.53  % (31701)Time elapsed: 0.101 s
% 0.21/0.53  % (31701)------------------------------
% 0.21/0.53  % (31701)------------------------------
% 0.21/0.53  % (31692)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31702)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (31693)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (31713)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31713)Memory used [KB]: 10746
% 0.21/0.54  % (31713)Time elapsed: 0.118 s
% 0.21/0.54  % (31713)------------------------------
% 0.21/0.54  % (31713)------------------------------
% 0.21/0.54  % (31693)Refutation not found, incomplete strategy% (31693)------------------------------
% 0.21/0.54  % (31693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31693)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31693)Memory used [KB]: 10746
% 0.21/0.54  % (31693)Time elapsed: 0.125 s
% 0.21/0.54  % (31693)------------------------------
% 0.21/0.54  % (31693)------------------------------
% 0.21/0.54  % (31697)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (31699)Refutation not found, incomplete strategy% (31699)------------------------------
% 0.21/0.54  % (31699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31699)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31699)Memory used [KB]: 11129
% 0.21/0.54  % (31699)Time elapsed: 0.130 s
% 0.21/0.54  % (31699)------------------------------
% 0.21/0.54  % (31699)------------------------------
% 0.21/0.54  % (31698)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (31712)Refutation not found, incomplete strategy% (31712)------------------------------
% 0.21/0.54  % (31712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (31712)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (31712)Memory used [KB]: 1791
% 0.21/0.54  % (31712)Time elapsed: 0.082 s
% 0.21/0.54  % (31712)------------------------------
% 0.21/0.54  % (31712)------------------------------
% 0.21/0.55  % (31694)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (31703)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (31720)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.55  % (31706)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.55  % (31716)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.56  % (31719)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.56  % (31707)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.56  % (31714)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.56  % (31700)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.56  % (31717)Refutation not found, incomplete strategy% (31717)------------------------------
% 1.53/0.56  % (31717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (31717)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (31717)Memory used [KB]: 11001
% 1.53/0.56  % (31717)Time elapsed: 0.142 s
% 1.53/0.56  % (31717)------------------------------
% 1.53/0.56  % (31717)------------------------------
% 1.53/0.57  % (31695)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f378,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(avatar_sat_refutation,[],[f126,f130,f145,f157,f203,f213,f274,f317,f345,f363,f367,f371,f377])).
% 1.53/0.57  fof(f377,plain,(
% 1.53/0.57    spl5_1 | ~spl5_10 | ~spl5_20),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f375])).
% 1.53/0.57  fof(f375,plain,(
% 1.53/0.57    $false | (spl5_1 | ~spl5_10 | ~spl5_20)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f276,f280,f285,f362])).
% 1.53/0.57  fof(f362,plain,(
% 1.53/0.57    ( ! [X0] : (v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl5_20),
% 1.53/0.57    inference(avatar_component_clause,[],[f361])).
% 1.53/0.57  fof(f361,plain,(
% 1.53/0.57    spl5_20 <=> ! [X0] : (v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.53/0.57  fof(f285,plain,(
% 1.53/0.57    ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl5_1 | ~spl5_10)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f70,f278,f238])).
% 1.53/0.57  fof(f238,plain,(
% 1.53/0.57    ( ! [X1] : (v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | ~spl5_10),
% 1.53/0.57    inference(backward_demodulation,[],[f212,f219])).
% 1.53/0.57  fof(f219,plain,(
% 1.53/0.57    u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f90,f89,f39])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 1.53/0.57    inference(cnf_transformation,[],[f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.53/0.57    inference(ennf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.53/0.57  fof(f89,plain,(
% 1.53/0.57    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f82,f83,f41])).
% 1.53/0.57  fof(f41,plain,(
% 1.53/0.57    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 1.53/0.57    inference(flattening,[],[f15])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 1.53/0.57  fof(f83,plain,(
% 1.53/0.57    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f68,f49])).
% 1.53/0.57  fof(f49,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f21])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.53/0.57    inference(ennf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 1.53/0.57  fof(f68,plain,(
% 1.53/0.57    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f34,f46])).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f19])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f5])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.53/0.57  fof(f34,plain,(
% 1.53/0.57    l1_pre_topc(sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,plain,(
% 1.53/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.53/0.57    inference(flattening,[],[f10])).
% 1.53/0.57  fof(f10,plain,(
% 1.53/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f9])).
% 1.53/0.57  fof(f9,negated_conjecture,(
% 1.53/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 1.53/0.57    inference(negated_conjecture,[],[f8])).
% 1.53/0.57  fof(f8,conjecture,(
% 1.53/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 1.53/0.57  fof(f82,plain,(
% 1.53/0.57    v1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f68,f48])).
% 1.53/0.57  fof(f48,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | v1_pre_topc(g1_pre_topc(X0,X1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f21])).
% 1.53/0.57  fof(f90,plain,(
% 1.53/0.57    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f83,f46])).
% 1.53/0.57  fof(f212,plain,(
% 1.53/0.57    ( ! [X1] : (v4_pre_topc(X1,sK0) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ) | ~spl5_10),
% 1.53/0.57    inference(avatar_component_clause,[],[f211])).
% 1.53/0.57  fof(f211,plain,(
% 1.53/0.57    spl5_10 <=> ! [X1] : (~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.53/0.57  fof(f278,plain,(
% 1.53/0.57    ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | spl5_1),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f28,f32,f34,f29,f30,f121,f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.53/0.57    inference(flattening,[],[f12])).
% 1.53/0.57  fof(f12,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 1.53/0.57  fof(f121,plain,(
% 1.53/0.57    ~v5_pre_topc(sK2,sK0,sK1) | spl5_1),
% 1.53/0.57    inference(avatar_component_clause,[],[f119])).
% 1.53/0.57  fof(f119,plain,(
% 1.53/0.57    spl5_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f29,plain,(
% 1.53/0.57    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    l1_pre_topc(sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f28,plain,(
% 1.53/0.57    v1_funct_1(sK2)),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f70,plain,(
% 1.53/0.57    ( ! [X0] : (m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f30,f47])).
% 1.53/0.57  fof(f47,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f20])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.57    inference(ennf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.53/0.57  fof(f280,plain,(
% 1.53/0.57    v4_pre_topc(sK4(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_1),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f31,f32,f277,f276,f44])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f18])).
% 1.53/0.57  fof(f18,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.53/0.57    inference(flattening,[],[f17])).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).
% 1.53/0.57  % (31705)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.57  fof(f277,plain,(
% 1.53/0.57    v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | spl5_1),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f28,f34,f32,f29,f30,f121,f37])).
% 1.53/0.57  fof(f37,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v4_pre_topc(sK4(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f31,plain,(
% 1.53/0.57    v2_pre_topc(sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f276,plain,(
% 1.53/0.57    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_1),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f28,f34,f32,f29,f30,f121,f36])).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f371,plain,(
% 1.53/0.57    spl5_19),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f368])).
% 1.53/0.57  fof(f368,plain,(
% 1.53/0.57    $false | spl5_19),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f30,f359])).
% 1.53/0.57  fof(f359,plain,(
% 1.53/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl5_19),
% 1.53/0.57    inference(avatar_component_clause,[],[f357])).
% 1.53/0.57  fof(f357,plain,(
% 1.53/0.57    spl5_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.53/0.57  fof(f367,plain,(
% 1.53/0.57    spl5_18),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f364])).
% 1.53/0.57  fof(f364,plain,(
% 1.53/0.57    $false | spl5_18),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f29,f355])).
% 1.53/0.57  fof(f355,plain,(
% 1.53/0.57    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | spl5_18),
% 1.53/0.57    inference(avatar_component_clause,[],[f353])).
% 1.53/0.57  fof(f353,plain,(
% 1.53/0.57    spl5_18 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.53/0.57  fof(f363,plain,(
% 1.53/0.57    ~spl5_14 | ~spl5_16 | ~spl5_18 | ~spl5_19 | spl5_20 | ~spl5_2),
% 1.53/0.57    inference(avatar_split_clause,[],[f302,f123,f361,f357,f353,f332,f304])).
% 1.53/0.57  fof(f304,plain,(
% 1.53/0.57    spl5_14 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.53/0.57  fof(f332,plain,(
% 1.53/0.57    spl5_16 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.53/0.57  fof(f123,plain,(
% 1.53/0.57    spl5_2 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.53/0.57  fof(f302,plain,(
% 1.53/0.57    ( ! [X0] : (v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_2),
% 1.53/0.57    inference(forward_demodulation,[],[f301,f219])).
% 1.53/0.57  fof(f301,plain,(
% 1.53/0.57    ( ! [X0] : (v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_2),
% 1.53/0.57    inference(forward_demodulation,[],[f300,f170])).
% 1.53/0.57  fof(f170,plain,(
% 1.53/0.57    u1_struct_0(sK1) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f80,f79,f39])).
% 1.53/0.57  fof(f79,plain,(
% 1.53/0.57    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f72,f73,f41])).
% 1.53/0.57  fof(f73,plain,(
% 1.53/0.57    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f62,f49])).
% 1.53/0.57  fof(f62,plain,(
% 1.53/0.57    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f32,f46])).
% 1.53/0.57  fof(f72,plain,(
% 1.53/0.57    v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f62,f48])).
% 1.53/0.57  fof(f80,plain,(
% 1.53/0.57    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f73,f46])).
% 1.53/0.57  fof(f300,plain,(
% 1.53/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_2),
% 1.53/0.57    inference(forward_demodulation,[],[f299,f170])).
% 1.53/0.57  fof(f299,plain,(
% 1.53/0.57    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_2),
% 1.53/0.57    inference(forward_demodulation,[],[f298,f219])).
% 1.53/0.57  fof(f298,plain,(
% 1.53/0.57    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_2),
% 1.53/0.57    inference(forward_demodulation,[],[f297,f170])).
% 1.53/0.57  fof(f297,plain,(
% 1.53/0.57    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_2),
% 1.53/0.57    inference(forward_demodulation,[],[f296,f219])).
% 1.53/0.57  fof(f296,plain,(
% 1.53/0.57    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_2),
% 1.53/0.57    inference(forward_demodulation,[],[f293,f170])).
% 1.53/0.57  fof(f293,plain,(
% 1.53/0.57    ( ! [X0] : (~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_2),
% 1.53/0.57    inference(resolution,[],[f55,f124])).
% 1.53/0.57  fof(f124,plain,(
% 1.53/0.57    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_2),
% 1.53/0.57    inference(avatar_component_clause,[],[f123])).
% 1.53/0.57  fof(f55,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~v5_pre_topc(sK2,X1,X0) | ~l1_pre_topc(X1) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2,X2),X1) | ~l1_pre_topc(X0)) )),
% 1.53/0.57    inference(resolution,[],[f28,f35])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X3,X1) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f345,plain,(
% 1.53/0.57    spl5_16),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f341])).
% 1.53/0.57  fof(f341,plain,(
% 1.53/0.57    $false | spl5_16),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f68,f334,f49])).
% 1.53/0.57  fof(f334,plain,(
% 1.53/0.57    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_16),
% 1.53/0.57    inference(avatar_component_clause,[],[f332])).
% 1.53/0.57  fof(f317,plain,(
% 1.53/0.57    spl5_14),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f313])).
% 1.53/0.57  fof(f313,plain,(
% 1.53/0.57    $false | spl5_14),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f62,f306,f49])).
% 1.53/0.57  fof(f306,plain,(
% 1.53/0.57    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_14),
% 1.53/0.57    inference(avatar_component_clause,[],[f304])).
% 1.53/0.57  fof(f274,plain,(
% 1.53/0.57    ~spl5_1 | spl5_2 | ~spl5_9),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f271])).
% 1.53/0.57  fof(f271,plain,(
% 1.53/0.57    $false | (~spl5_1 | spl5_2 | ~spl5_9)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f34,f33,f208,f70,f237,f44])).
% 1.53/0.57  fof(f237,plain,(
% 1.53/0.57    ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_2),
% 1.53/0.57    inference(backward_demodulation,[],[f189,f219])).
% 1.53/0.57  fof(f189,plain,(
% 1.53/0.57    ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_2),
% 1.53/0.57    inference(backward_demodulation,[],[f133,f170])).
% 1.53/0.57  fof(f133,plain,(
% 1.53/0.57    ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_2),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f28,f73,f83,f51,f50,f125,f38])).
% 1.53/0.57  fof(f125,plain,(
% 1.53/0.57    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_2),
% 1.53/0.57    inference(avatar_component_clause,[],[f123])).
% 1.53/0.57  fof(f50,plain,(
% 1.53/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 1.53/0.57    inference(forward_demodulation,[],[f26,f27])).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    sK2 = sK3),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f51,plain,(
% 1.53/0.57    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 1.53/0.57    inference(forward_demodulation,[],[f25,f27])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f208,plain,(
% 1.53/0.57    v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0) | (~spl5_1 | spl5_2 | ~spl5_9)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f34,f32,f28,f120,f29,f30,f188,f204,f35])).
% 1.53/0.57  fof(f204,plain,(
% 1.53/0.57    v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1) | (spl5_2 | ~spl5_9)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f188,f132,f202])).
% 1.53/0.57  fof(f202,plain,(
% 1.53/0.57    ( ! [X1] : (v4_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | ~spl5_9),
% 1.53/0.57    inference(avatar_component_clause,[],[f201])).
% 1.53/0.57  fof(f201,plain,(
% 1.53/0.57    spl5_9 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(X1,sK1) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.53/0.57  fof(f132,plain,(
% 1.53/0.57    v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_2),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f28,f73,f83,f51,f50,f125,f37])).
% 1.53/0.57  fof(f188,plain,(
% 1.53/0.57    m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_2),
% 1.53/0.57    inference(backward_demodulation,[],[f131,f170])).
% 1.53/0.57  fof(f131,plain,(
% 1.53/0.57    m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | spl5_2),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f28,f73,f83,f51,f50,f125,f36])).
% 1.53/0.57  fof(f120,plain,(
% 1.53/0.57    v5_pre_topc(sK2,sK0,sK1) | ~spl5_1),
% 1.53/0.57    inference(avatar_component_clause,[],[f119])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    v2_pre_topc(sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f213,plain,(
% 1.53/0.57    spl5_10 | ~spl5_6),
% 1.53/0.57    inference(avatar_split_clause,[],[f65,f150,f211])).
% 1.53/0.57  fof(f150,plain,(
% 1.53/0.57    spl5_6 <=> l1_pre_topc(sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.53/0.57  fof(f65,plain,(
% 1.53/0.57    ( ! [X1] : (~l1_pre_topc(sK0) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | v4_pre_topc(X1,sK0)) )),
% 1.53/0.57    inference(resolution,[],[f33,f43])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | v4_pre_topc(X1,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f18])).
% 1.53/0.57  fof(f203,plain,(
% 1.53/0.57    ~spl5_4 | spl5_9),
% 1.53/0.57    inference(avatar_split_clause,[],[f186,f201,f138])).
% 1.53/0.57  fof(f138,plain,(
% 1.53/0.57    spl5_4 <=> l1_pre_topc(sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.53/0.57  fof(f186,plain,(
% 1.53/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v4_pre_topc(X1,sK1)) )),
% 1.53/0.57    inference(backward_demodulation,[],[f59,f170])).
% 1.53/0.57  fof(f59,plain,(
% 1.53/0.57    ( ! [X1] : (~l1_pre_topc(sK1) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | v4_pre_topc(X1,sK1)) )),
% 1.53/0.57    inference(resolution,[],[f31,f43])).
% 1.53/0.57  fof(f157,plain,(
% 1.53/0.57    spl5_6),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f154])).
% 1.53/0.57  fof(f154,plain,(
% 1.53/0.57    $false | spl5_6),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f34,f152])).
% 1.53/0.57  fof(f152,plain,(
% 1.53/0.57    ~l1_pre_topc(sK0) | spl5_6),
% 1.53/0.57    inference(avatar_component_clause,[],[f150])).
% 1.53/0.57  fof(f145,plain,(
% 1.53/0.57    spl5_4),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f142])).
% 1.53/0.57  fof(f142,plain,(
% 1.53/0.57    $false | spl5_4),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f32,f140])).
% 1.53/0.57  fof(f140,plain,(
% 1.53/0.57    ~l1_pre_topc(sK1) | spl5_4),
% 1.53/0.57    inference(avatar_component_clause,[],[f138])).
% 1.53/0.57  fof(f130,plain,(
% 1.53/0.57    spl5_1 | spl5_2),
% 1.53/0.57    inference(avatar_split_clause,[],[f54,f123,f119])).
% 1.53/0.57  fof(f54,plain,(
% 1.53/0.57    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.53/0.57    inference(forward_demodulation,[],[f22,f27])).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f126,plain,(
% 1.53/0.57    ~spl5_1 | ~spl5_2),
% 1.53/0.57    inference(avatar_split_clause,[],[f53,f123,f119])).
% 1.53/0.57  fof(f53,plain,(
% 1.53/0.57    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.53/0.57    inference(forward_demodulation,[],[f23,f27])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (31695)------------------------------
% 1.53/0.57  % (31695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (31695)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (31695)Memory used [KB]: 6524
% 1.53/0.57  % (31695)Time elapsed: 0.123 s
% 1.53/0.57  % (31695)------------------------------
% 1.53/0.57  % (31695)------------------------------
% 1.53/0.57  % (31690)Success in time 0.208 s
%------------------------------------------------------------------------------
