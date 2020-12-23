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
% DateTime   : Thu Dec  3 13:09:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 535 expanded)
%              Number of leaves         :   39 ( 255 expanded)
%              Depth                    :   11
%              Number of atoms          :  760 (3726 expanded)
%              Number of equality atoms :   24 ( 193 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f64,f69,f74,f79,f89,f94,f99,f104,f109,f114,f127,f132,f138,f150,f164,f165,f180,f187,f204,f209,f216,f236,f238,f255,f266,f276,f284,f289,f308])).

fof(f308,plain,
    ( spl5_34
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_35
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f307,f286,f281,f177,f135,f129,f124,f111,f96,f269])).

fof(f269,plain,
    ( spl5_34
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f96,plain,
    ( spl5_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f111,plain,
    ( spl5_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f124,plain,
    ( spl5_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f129,plain,
    ( spl5_15
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f135,plain,
    ( spl5_16
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f177,plain,
    ( spl5_22
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f281,plain,
    ( spl5_35
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f286,plain,
    ( spl5_36
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f307,plain,
    ( v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_35
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f303,f152])).

fof(f152,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0)
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f126,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f303,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_22
    | ~ spl5_35
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f113,f179,f137,f131,f283,f126,f288,f168])).

fof(f168,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v5_pre_topc(sK2,X2,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v4_pre_topc(X0,X1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK2,X0),X2)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X2) )
    | ~ spl5_9 ),
    inference(resolution,[],[f44,f98])).

fof(f98,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
                    & v4_pre_topc(sK4(X0,X1,X2),X1)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v4_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

% (29759)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f288,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f286])).

fof(f283,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f281])).

fof(f131,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f137,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f179,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f177])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f289,plain,
    ( spl5_36
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_20
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f278,f263,f161,f106,f101,f286])).

fof(f101,plain,
    ( spl5_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f106,plain,
    ( spl5_11
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f161,plain,
    ( spl5_20
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f263,plain,
    ( spl5_33
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f278,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_20
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f108,f103,f163,f265,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f265,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f263])).

% (29755)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
fof(f163,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f161])).

fof(f103,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f284,plain,
    ( spl5_35
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_20
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f279,f263,f161,f106,f101,f281])).

fof(f279,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_20
    | ~ spl5_33 ),
    inference(unit_resulting_resolution,[],[f108,f103,f163,f265,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f276,plain,
    ( ~ spl5_12
    | ~ spl5_10
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_34
    | spl5_1
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f275,f96,f86,f56,f269,f86,f91,f101,f111])).

fof(f91,plain,
    ( spl5_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f56,plain,
    ( spl5_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f86,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f275,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f261,f151])).

fof(f151,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f88,f48])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f261,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | spl5_1
    | ~ spl5_9 ),
    inference(resolution,[],[f58,f167])).

fof(f167,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f47,f98])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f266,plain,
    ( spl5_33
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f259,f111,f101,f96,f91,f86,f56,f263])).

fof(f259,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f113,f103,f98,f93,f88,f58,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f255,plain,
    ( ~ spl5_11
    | ~ spl5_10
    | ~ spl5_25
    | ~ spl5_26
    | spl5_31 ),
    inference(avatar_split_clause,[],[f254,f233,f206,f201,f101,f106])).

fof(f201,plain,
    ( spl5_25
  <=> v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f206,plain,
    ( spl5_26
  <=> m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f233,plain,
    ( spl5_31
  <=> v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f254,plain,
    ( ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl5_31 ),
    inference(resolution,[],[f235,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f235,plain,
    ( ~ v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | spl5_31 ),
    inference(avatar_component_clause,[],[f233])).

fof(f238,plain,
    ( ~ spl5_11
    | ~ spl5_10
    | ~ spl5_25
    | ~ spl5_26
    | spl5_30 ),
    inference(avatar_split_clause,[],[f237,f229,f206,f201,f101,f106])).

fof(f229,plain,
    ( spl5_30
  <=> m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f237,plain,
    ( ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl5_30 ),
    inference(resolution,[],[f231,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f231,plain,
    ( ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f229])).

fof(f236,plain,
    ( ~ spl5_30
    | ~ spl5_31
    | spl5_23
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f227,f214,f184,f233,f229])).

fof(f184,plain,
    ( spl5_23
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f214,plain,
    ( spl5_27
  <=> ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f227,plain,
    ( ~ v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_23
    | ~ spl5_27 ),
    inference(resolution,[],[f215,f186])).

fof(f186,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f184])).

fof(f215,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( ~ spl5_12
    | ~ spl5_10
    | ~ spl5_7
    | ~ spl5_1
    | spl5_27
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f212,f96,f91,f86,f214,f56,f86,f101,f111])).

fof(f212,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v4_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f210,f151])).

% (29762)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f210,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(resolution,[],[f168,f93])).

fof(f209,plain,
    ( spl5_26
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f188,f177,f135,f129,f124,f111,f96,f206])).

fof(f188,plain,
    ( m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f113,f98,f136,f131,f126,f179,f45])).

fof(f136,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f204,plain,
    ( spl5_25
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f189,f177,f135,f129,f124,f111,f96,f201])).

fof(f189,plain,
    ( v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_15
    | spl5_16
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f113,f98,f136,f131,f126,f179,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f187,plain,
    ( ~ spl5_12
    | ~ spl5_22
    | ~ spl5_15
    | ~ spl5_14
    | ~ spl5_23
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(avatar_split_clause,[],[f182,f135,f124,f96,f184,f124,f129,f177,f111])).

fof(f182,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | ~ spl5_14
    | spl5_16 ),
    inference(forward_demodulation,[],[f181,f152])).

fof(f181,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_9
    | spl5_16 ),
    inference(resolution,[],[f167,f136])).

fof(f180,plain,
    ( spl5_22
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f175,f147,f177])).

fof(f147,plain,
    ( spl5_18
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f175,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f149,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f149,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f147])).

fof(f165,plain,
    ( sK2 != sK3
    | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f164,plain,
    ( spl5_20
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f159,f111,f101,f96,f91,f86,f56,f161])).

fof(f159,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | spl5_1
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f113,f103,f98,f58,f93,f88,f46])).

fof(f150,plain,
    ( spl5_18
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f139,f101,f147])).

fof(f139,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f103,f54])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f138,plain,
    ( spl5_16
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f133,f66,f60,f135])).

fof(f60,plain,
    ( spl5_2
  <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f66,plain,
    ( spl5_3
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f133,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f61,f68])).

fof(f68,plain,
    ( sK2 = sK3
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f61,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f132,plain,
    ( spl5_15
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f121,f76,f66,f129])).

fof(f76,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f121,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f78,f68])).

fof(f78,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f127,plain,
    ( spl5_14
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f120,f71,f66,f124])).

fof(f71,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f73,f68])).

% (29759)Refutation not found, incomplete strategy% (29759)------------------------------
% (29759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29759)Termination reason: Refutation not found, incomplete strategy

% (29759)Memory used [KB]: 6140
% (29759)Time elapsed: 0.116 s
% (29759)------------------------------
% (29759)------------------------------
% (29755)Refutation not found, incomplete strategy% (29755)------------------------------
% (29755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29755)Termination reason: Refutation not found, incomplete strategy

% (29755)Memory used [KB]: 1663
% (29755)Time elapsed: 0.130 s
% (29755)------------------------------
% (29755)------------------------------
fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f114,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f32,f111])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f23,f22,f21,f20])).

% (29741)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f109,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f33,f106])).

fof(f33,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f34,f101])).

fof(f34,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f35,f96])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f36,f91])).

fof(f36,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f89,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f37,f86])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

% (29758)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
fof(f74,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f41,f66])).

fof(f41,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f42,f60,f56])).

fof(f42,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f43,f60,f56])).

fof(f43,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:08:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (29746)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.45  % (29754)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.46  % (29746)Refutation not found, incomplete strategy% (29746)------------------------------
% 0.19/0.46  % (29746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (29746)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (29746)Memory used [KB]: 6268
% 0.19/0.47  % (29746)Time elapsed: 0.051 s
% 0.19/0.47  % (29746)------------------------------
% 0.19/0.47  % (29746)------------------------------
% 0.19/0.49  % (29744)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.19/0.50  % (29739)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.19/0.50  % (29748)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.19/0.50  % (29743)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.19/0.50  % (29745)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.51  % (29740)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.51  % (29747)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.19/0.51  % (29745)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % (29753)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.51  % (29749)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.51  % (29742)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.19/0.51  % (29752)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.19/0.51  % (29747)Refutation not found, incomplete strategy% (29747)------------------------------
% 0.19/0.51  % (29747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (29747)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (29747)Memory used [KB]: 10618
% 0.19/0.51  % (29747)Time elapsed: 0.123 s
% 0.19/0.51  % (29747)------------------------------
% 0.19/0.51  % (29747)------------------------------
% 0.19/0.51  % (29742)Refutation not found, incomplete strategy% (29742)------------------------------
% 0.19/0.51  % (29742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (29742)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (29742)Memory used [KB]: 10618
% 0.19/0.51  % (29742)Time elapsed: 0.107 s
% 0.19/0.51  % (29742)------------------------------
% 0.19/0.51  % (29742)------------------------------
% 0.19/0.51  % (29749)Refutation not found, incomplete strategy% (29749)------------------------------
% 0.19/0.51  % (29749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (29749)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (29749)Memory used [KB]: 10618
% 0.19/0.51  % (29749)Time elapsed: 0.093 s
% 0.19/0.51  % (29749)------------------------------
% 0.19/0.51  % (29749)------------------------------
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f309,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f63,f64,f69,f74,f79,f89,f94,f99,f104,f109,f114,f127,f132,f138,f150,f164,f165,f180,f187,f204,f209,f216,f236,f238,f255,f266,f276,f284,f289,f308])).
% 0.19/0.52  fof(f308,plain,(
% 0.19/0.52    spl5_34 | ~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_15 | ~spl5_16 | ~spl5_22 | ~spl5_35 | ~spl5_36),
% 0.19/0.52    inference(avatar_split_clause,[],[f307,f286,f281,f177,f135,f129,f124,f111,f96,f269])).
% 0.19/0.52  fof(f269,plain,(
% 0.19/0.52    spl5_34 <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.19/0.52  fof(f96,plain,(
% 0.19/0.52    spl5_9 <=> v1_funct_1(sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.19/0.52  fof(f111,plain,(
% 0.19/0.52    spl5_12 <=> l1_pre_topc(sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.52  fof(f124,plain,(
% 0.19/0.52    spl5_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.19/0.52  fof(f129,plain,(
% 0.19/0.52    spl5_15 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.19/0.52  fof(f135,plain,(
% 0.19/0.52    spl5_16 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.19/0.52  fof(f177,plain,(
% 0.19/0.52    spl5_22 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.19/0.52  fof(f281,plain,(
% 0.19/0.52    spl5_35 <=> v4_pre_topc(sK4(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.19/0.52  fof(f286,plain,(
% 0.19/0.52    spl5_36 <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.19/0.52  fof(f307,plain,(
% 0.19/0.52    v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) | (~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_15 | ~spl5_16 | ~spl5_22 | ~spl5_35 | ~spl5_36)),
% 0.19/0.52    inference(forward_demodulation,[],[f303,f152])).
% 0.19/0.52  fof(f152,plain,(
% 0.19/0.52    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X0)) ) | ~spl5_14),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f126,f48])).
% 0.19/0.52  fof(f48,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.19/0.52  fof(f126,plain,(
% 0.19/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl5_14),
% 0.19/0.52    inference(avatar_component_clause,[],[f124])).
% 0.19/0.52  fof(f303,plain,(
% 0.19/0.52    v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,sK4(sK0,sK1,sK2)),sK0) | (~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_15 | ~spl5_16 | ~spl5_22 | ~spl5_35 | ~spl5_36)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f113,f179,f137,f131,f283,f126,f288,f168])).
% 0.19/0.52  fof(f168,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(sK2,X2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v4_pre_topc(X0,X1) | v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),sK2,X0),X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X2)) ) | ~spl5_9),
% 0.19/0.52    inference(resolution,[],[f44,f98])).
% 0.19/0.52  fof(f98,plain,(
% 0.19/0.52    v1_funct_1(sK2) | ~spl5_9),
% 0.19/0.52    inference(avatar_component_clause,[],[f96])).
% 0.19/0.52  fof(f44,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v4_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X2,X1,X0] : (? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) & v4_pre_topc(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v4_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(rectify,[],[f25])).
% 0.19/0.52  % (29759)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v4_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f11])).
% 0.19/0.52  fof(f11,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.19/0.52  fof(f288,plain,(
% 0.19/0.52    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~spl5_36),
% 0.19/0.52    inference(avatar_component_clause,[],[f286])).
% 0.19/0.52  fof(f283,plain,(
% 0.19/0.52    v4_pre_topc(sK4(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_35),
% 0.19/0.52    inference(avatar_component_clause,[],[f281])).
% 0.19/0.52  fof(f131,plain,(
% 0.19/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl5_15),
% 0.19/0.52    inference(avatar_component_clause,[],[f129])).
% 0.19/0.52  fof(f137,plain,(
% 0.19/0.52    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_16),
% 0.19/0.52    inference(avatar_component_clause,[],[f135])).
% 0.19/0.52  fof(f179,plain,(
% 0.19/0.52    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_22),
% 0.19/0.52    inference(avatar_component_clause,[],[f177])).
% 0.19/0.52  fof(f113,plain,(
% 0.19/0.52    l1_pre_topc(sK0) | ~spl5_12),
% 0.19/0.52    inference(avatar_component_clause,[],[f111])).
% 0.19/0.52  fof(f289,plain,(
% 0.19/0.52    spl5_36 | ~spl5_10 | ~spl5_11 | ~spl5_20 | ~spl5_33),
% 0.19/0.52    inference(avatar_split_clause,[],[f278,f263,f161,f106,f101,f286])).
% 0.19/0.52  fof(f101,plain,(
% 0.19/0.52    spl5_10 <=> l1_pre_topc(sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.19/0.52  fof(f106,plain,(
% 0.19/0.52    spl5_11 <=> v2_pre_topc(sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.19/0.52  fof(f161,plain,(
% 0.19/0.52    spl5_20 <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.19/0.52  fof(f263,plain,(
% 0.19/0.52    spl5_33 <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.19/0.52  fof(f278,plain,(
% 0.19/0.52    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl5_10 | ~spl5_11 | ~spl5_20 | ~spl5_33)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f108,f103,f163,f265,f51])).
% 0.19/0.52  fof(f51,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).
% 0.19/0.52  fof(f265,plain,(
% 0.19/0.52    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl5_33),
% 0.19/0.52    inference(avatar_component_clause,[],[f263])).
% 0.19/0.52  % (29755)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.52  fof(f163,plain,(
% 0.19/0.52    v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | ~spl5_20),
% 0.19/0.52    inference(avatar_component_clause,[],[f161])).
% 0.19/0.52  fof(f103,plain,(
% 0.19/0.52    l1_pre_topc(sK1) | ~spl5_10),
% 0.19/0.52    inference(avatar_component_clause,[],[f101])).
% 0.19/0.52  fof(f108,plain,(
% 0.19/0.52    v2_pre_topc(sK1) | ~spl5_11),
% 0.19/0.52    inference(avatar_component_clause,[],[f106])).
% 0.19/0.52  fof(f284,plain,(
% 0.19/0.52    spl5_35 | ~spl5_10 | ~spl5_11 | ~spl5_20 | ~spl5_33),
% 0.19/0.52    inference(avatar_split_clause,[],[f279,f263,f161,f106,f101,f281])).
% 0.19/0.52  fof(f279,plain,(
% 0.19/0.52    v4_pre_topc(sK4(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_10 | ~spl5_11 | ~spl5_20 | ~spl5_33)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f108,f103,f163,f265,f50])).
% 0.19/0.52  fof(f50,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f276,plain,(
% 0.19/0.52    ~spl5_12 | ~spl5_10 | ~spl5_8 | ~spl5_7 | ~spl5_34 | spl5_1 | ~spl5_7 | ~spl5_9),
% 0.19/0.52    inference(avatar_split_clause,[],[f275,f96,f86,f56,f269,f86,f91,f101,f111])).
% 0.19/0.52  fof(f91,plain,(
% 0.19/0.52    spl5_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    spl5_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.52  fof(f86,plain,(
% 0.19/0.52    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.52  fof(f275,plain,(
% 0.19/0.52    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_7 | ~spl5_9)),
% 0.19/0.52    inference(forward_demodulation,[],[f261,f151])).
% 0.19/0.52  fof(f151,plain,(
% 0.19/0.52    ( ! [X0] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl5_7),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f88,f48])).
% 0.19/0.52  fof(f88,plain,(
% 0.19/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_7),
% 0.19/0.52    inference(avatar_component_clause,[],[f86])).
% 0.19/0.52  fof(f261,plain,(
% 0.19/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | (spl5_1 | ~spl5_9)),
% 0.19/0.52    inference(resolution,[],[f58,f167])).
% 0.19/0.52  fof(f167,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v5_pre_topc(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK4(X0,X1,sK2)),X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) ) | ~spl5_9),
% 0.19/0.52    inference(resolution,[],[f47,f98])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ~v5_pre_topc(sK2,sK0,sK1) | spl5_1),
% 0.19/0.52    inference(avatar_component_clause,[],[f56])).
% 0.19/0.52  fof(f266,plain,(
% 0.19/0.52    spl5_33 | spl5_1 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_12),
% 0.19/0.52    inference(avatar_split_clause,[],[f259,f111,f101,f96,f91,f86,f56,f263])).
% 0.19/0.52  fof(f259,plain,(
% 0.19/0.52    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | (spl5_1 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f113,f103,f98,f93,f88,f58,f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f93,plain,(
% 0.19/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_8),
% 0.19/0.52    inference(avatar_component_clause,[],[f91])).
% 0.19/0.52  fof(f255,plain,(
% 0.19/0.52    ~spl5_11 | ~spl5_10 | ~spl5_25 | ~spl5_26 | spl5_31),
% 0.19/0.52    inference(avatar_split_clause,[],[f254,f233,f206,f201,f101,f106])).
% 0.19/0.52  fof(f201,plain,(
% 0.19/0.52    spl5_25 <=> v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.19/0.52  fof(f206,plain,(
% 0.19/0.52    spl5_26 <=> m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.19/0.52  fof(f233,plain,(
% 0.19/0.52    spl5_31 <=> v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.19/0.52  fof(f254,plain,(
% 0.19/0.52    ~m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl5_31),
% 0.19/0.52    inference(resolution,[],[f235,f52])).
% 0.19/0.52  fof(f52,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f235,plain,(
% 0.19/0.52    ~v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1) | spl5_31),
% 0.19/0.52    inference(avatar_component_clause,[],[f233])).
% 0.19/0.52  fof(f238,plain,(
% 0.19/0.52    ~spl5_11 | ~spl5_10 | ~spl5_25 | ~spl5_26 | spl5_30),
% 0.19/0.52    inference(avatar_split_clause,[],[f237,f229,f206,f201,f101,f106])).
% 0.19/0.52  fof(f229,plain,(
% 0.19/0.52    spl5_30 <=> m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.19/0.52  fof(f237,plain,(
% 0.19/0.52    ~m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl5_30),
% 0.19/0.52    inference(resolution,[],[f231,f53])).
% 0.19/0.52  fof(f53,plain,(
% 0.19/0.52    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f231,plain,(
% 0.19/0.52    ~m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_30),
% 0.19/0.52    inference(avatar_component_clause,[],[f229])).
% 0.19/0.52  fof(f236,plain,(
% 0.19/0.52    ~spl5_30 | ~spl5_31 | spl5_23 | ~spl5_27),
% 0.19/0.52    inference(avatar_split_clause,[],[f227,f214,f184,f233,f229])).
% 0.19/0.52  fof(f184,plain,(
% 0.19/0.52    spl5_23 <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.19/0.52  fof(f214,plain,(
% 0.19/0.52    spl5_27 <=> ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.19/0.52  fof(f227,plain,(
% 0.19/0.52    ~v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1) | ~m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1))) | (spl5_23 | ~spl5_27)),
% 0.19/0.52    inference(resolution,[],[f215,f186])).
% 0.19/0.52  fof(f186,plain,(
% 0.19/0.52    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0) | spl5_23),
% 0.19/0.52    inference(avatar_component_clause,[],[f184])).
% 0.19/0.52  fof(f215,plain,(
% 0.19/0.52    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl5_27),
% 0.19/0.52    inference(avatar_component_clause,[],[f214])).
% 0.19/0.52  fof(f216,plain,(
% 0.19/0.52    ~spl5_12 | ~spl5_10 | ~spl5_7 | ~spl5_1 | spl5_27 | ~spl5_7 | ~spl5_8 | ~spl5_9),
% 0.19/0.52    inference(avatar_split_clause,[],[f212,f96,f91,f86,f214,f56,f86,f101,f111])).
% 0.19/0.52  fof(f212,plain,(
% 0.19/0.52    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v4_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) ) | (~spl5_7 | ~spl5_8 | ~spl5_9)),
% 0.19/0.52    inference(forward_demodulation,[],[f210,f151])).
% 0.19/0.52  % (29762)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.52  fof(f210,plain,(
% 0.19/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)) ) | (~spl5_8 | ~spl5_9)),
% 0.19/0.52    inference(resolution,[],[f168,f93])).
% 0.19/0.52  fof(f209,plain,(
% 0.19/0.52    spl5_26 | ~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_22),
% 0.19/0.52    inference(avatar_split_clause,[],[f188,f177,f135,f129,f124,f111,f96,f206])).
% 0.19/0.52  fof(f188,plain,(
% 0.19/0.52    m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | (~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_22)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f113,f98,f136,f131,f126,f179,f45])).
% 0.19/0.52  fof(f136,plain,(
% 0.19/0.52    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_16),
% 0.19/0.52    inference(avatar_component_clause,[],[f135])).
% 0.19/0.52  fof(f204,plain,(
% 0.19/0.52    spl5_25 | ~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_22),
% 0.19/0.52    inference(avatar_split_clause,[],[f189,f177,f135,f129,f124,f111,f96,f201])).
% 0.19/0.52  fof(f189,plain,(
% 0.19/0.52    v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_9 | ~spl5_12 | ~spl5_14 | ~spl5_15 | spl5_16 | ~spl5_22)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f113,f98,f136,f131,f126,f179,f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (v4_pre_topc(sK4(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f187,plain,(
% 0.19/0.52    ~spl5_12 | ~spl5_22 | ~spl5_15 | ~spl5_14 | ~spl5_23 | ~spl5_9 | ~spl5_14 | spl5_16),
% 0.19/0.52    inference(avatar_split_clause,[],[f182,f135,f124,f96,f184,f124,f129,f177,f111])).
% 0.19/0.52  fof(f182,plain,(
% 0.19/0.52    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | (~spl5_9 | ~spl5_14 | spl5_16)),
% 0.19/0.52    inference(forward_demodulation,[],[f181,f152])).
% 0.19/0.52  fof(f181,plain,(
% 0.19/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK0) | (~spl5_9 | spl5_16)),
% 0.19/0.52    inference(resolution,[],[f167,f136])).
% 0.19/0.52  fof(f180,plain,(
% 0.19/0.52    spl5_22 | ~spl5_18),
% 0.19/0.52    inference(avatar_split_clause,[],[f175,f147,f177])).
% 0.19/0.52  fof(f147,plain,(
% 0.19/0.52    spl5_18 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.19/0.52  fof(f175,plain,(
% 0.19/0.52    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_18),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f149,f49])).
% 0.19/0.52  fof(f49,plain,(
% 0.19/0.52    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,plain,(
% 0.19/0.52    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.19/0.52    inference(ennf_transformation,[],[f8])).
% 0.19/0.52  fof(f8,plain,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.19/0.52    inference(pure_predicate_removal,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.19/0.52  fof(f149,plain,(
% 0.19/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl5_18),
% 0.19/0.52    inference(avatar_component_clause,[],[f147])).
% 0.19/0.52  fof(f165,plain,(
% 0.19/0.52    sK2 != sK3 | v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.19/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.52  fof(f164,plain,(
% 0.19/0.52    spl5_20 | spl5_1 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_12),
% 0.19/0.52    inference(avatar_split_clause,[],[f159,f111,f101,f96,f91,f86,f56,f161])).
% 0.19/0.52  fof(f159,plain,(
% 0.19/0.52    v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | (spl5_1 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_12)),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f113,f103,f98,f58,f93,f88,f46])).
% 0.19/0.52  fof(f150,plain,(
% 0.19/0.52    spl5_18 | ~spl5_10),
% 0.19/0.52    inference(avatar_split_clause,[],[f139,f101,f147])).
% 0.19/0.52  fof(f139,plain,(
% 0.19/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~spl5_10),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f103,f54])).
% 0.19/0.52  fof(f54,plain,(
% 0.19/0.52    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.19/0.52  fof(f138,plain,(
% 0.19/0.52    spl5_16 | ~spl5_2 | ~spl5_3),
% 0.19/0.52    inference(avatar_split_clause,[],[f133,f66,f60,f135])).
% 0.19/0.52  fof(f60,plain,(
% 0.19/0.52    spl5_2 <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.52  fof(f66,plain,(
% 0.19/0.52    spl5_3 <=> sK2 = sK3),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.52  fof(f133,plain,(
% 0.19/0.52    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3)),
% 0.19/0.52    inference(forward_demodulation,[],[f61,f68])).
% 0.19/0.52  fof(f68,plain,(
% 0.19/0.52    sK2 = sK3 | ~spl5_3),
% 0.19/0.52    inference(avatar_component_clause,[],[f66])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_2),
% 0.19/0.52    inference(avatar_component_clause,[],[f60])).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    spl5_15 | ~spl5_3 | ~spl5_5),
% 0.19/0.52    inference(avatar_split_clause,[],[f121,f76,f66,f129])).
% 0.19/0.52  fof(f76,plain,(
% 0.19/0.52    spl5_5 <=> v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.52  fof(f121,plain,(
% 0.19/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_3 | ~spl5_5)),
% 0.19/0.52    inference(backward_demodulation,[],[f78,f68])).
% 0.19/0.52  fof(f78,plain,(
% 0.19/0.52    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl5_5),
% 0.19/0.52    inference(avatar_component_clause,[],[f76])).
% 0.19/0.52  fof(f127,plain,(
% 0.19/0.52    spl5_14 | ~spl5_3 | ~spl5_4),
% 0.19/0.52    inference(avatar_split_clause,[],[f120,f71,f66,f124])).
% 0.19/0.52  fof(f71,plain,(
% 0.19/0.52    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.52  fof(f120,plain,(
% 0.19/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl5_3 | ~spl5_4)),
% 0.19/0.52    inference(backward_demodulation,[],[f73,f68])).
% 0.19/0.52  % (29759)Refutation not found, incomplete strategy% (29759)------------------------------
% 0.19/0.52  % (29759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (29759)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (29759)Memory used [KB]: 6140
% 0.19/0.52  % (29759)Time elapsed: 0.116 s
% 0.19/0.52  % (29759)------------------------------
% 0.19/0.52  % (29759)------------------------------
% 0.19/0.52  % (29755)Refutation not found, incomplete strategy% (29755)------------------------------
% 0.19/0.52  % (29755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (29755)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (29755)Memory used [KB]: 1663
% 0.19/0.52  % (29755)Time elapsed: 0.130 s
% 0.19/0.52  % (29755)------------------------------
% 0.19/0.52  % (29755)------------------------------
% 0.19/0.52  fof(f73,plain,(
% 0.19/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl5_4),
% 0.19/0.52    inference(avatar_component_clause,[],[f71])).
% 0.19/0.52  fof(f114,plain,(
% 0.19/0.52    spl5_12),
% 0.19/0.52    inference(avatar_split_clause,[],[f32,f111])).
% 0.19/0.52  fof(f32,plain,(
% 0.19/0.52    l1_pre_topc(sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ((((~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.19/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f23,f22,f21,f20])).
% 0.19/0.52  % (29741)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ? [X3] : ((~v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 0.19/0.52    introduced(choice_axiom,[])).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.52    inference(nnf_transformation,[],[f10])).
% 0.19/0.52  fof(f10,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.52    inference(flattening,[],[f9])).
% 0.19/0.52  fof(f9,plain,(
% 0.19/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,negated_conjecture,(
% 0.19/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 0.19/0.52    inference(negated_conjecture,[],[f6])).
% 0.19/0.52  fof(f6,conjecture,(
% 0.19/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 0.19/0.52  fof(f109,plain,(
% 0.19/0.52    spl5_11),
% 0.19/0.52    inference(avatar_split_clause,[],[f33,f106])).
% 0.19/0.52  fof(f33,plain,(
% 0.19/0.52    v2_pre_topc(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f104,plain,(
% 0.19/0.52    spl5_10),
% 0.19/0.52    inference(avatar_split_clause,[],[f34,f101])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    l1_pre_topc(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f99,plain,(
% 0.19/0.52    spl5_9),
% 0.19/0.52    inference(avatar_split_clause,[],[f35,f96])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    v1_funct_1(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f94,plain,(
% 0.19/0.52    spl5_8),
% 0.19/0.52    inference(avatar_split_clause,[],[f36,f91])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f89,plain,(
% 0.19/0.52    spl5_7),
% 0.19/0.52    inference(avatar_split_clause,[],[f37,f86])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f79,plain,(
% 0.19/0.52    spl5_5),
% 0.19/0.52    inference(avatar_split_clause,[],[f39,f76])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  % (29758)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    spl5_4),
% 0.19/0.52    inference(avatar_split_clause,[],[f40,f71])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f69,plain,(
% 0.19/0.52    spl5_3),
% 0.19/0.52    inference(avatar_split_clause,[],[f41,f66])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    sK2 = sK3),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f64,plain,(
% 0.19/0.52    spl5_1 | spl5_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f42,f60,f56])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ~spl5_1 | ~spl5_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f43,f60,f56])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ~v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f24])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (29745)------------------------------
% 0.19/0.52  % (29745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (29745)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (29745)Memory used [KB]: 11001
% 0.19/0.52  % (29745)Time elapsed: 0.085 s
% 0.19/0.52  % (29745)------------------------------
% 0.19/0.52  % (29745)------------------------------
% 0.19/0.52  % (29738)Success in time 0.18 s
%------------------------------------------------------------------------------
