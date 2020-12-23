%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1132+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 492 expanded)
%              Number of leaves         :   27 ( 152 expanded)
%              Depth                    :   10
%              Number of atoms          :  584 (3353 expanded)
%              Number of equality atoms :   10 ( 198 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f246,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f52,f75,f90,f97,f105,f110,f116,f126,f133,f157,f161,f163,f165,f171,f177,f181,f183,f185,f192,f193,f214,f224,f232,f240])).

fof(f240,plain,
    ( ~ spl5_14
    | ~ spl5_16
    | spl5_7
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f239,f230,f108,f149,f143])).

fof(f143,plain,
    ( spl5_14
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f149,plain,
    ( spl5_16
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f108,plain,
    ( spl5_7
  <=> ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f230,plain,
    ( spl5_27
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1) )
    | ~ spl5_27 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_27 ),
    inference(resolution,[],[f231,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(ennf_transformation,[],[f6])).

% (24647)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f231,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v4_pre_topc(X0,sK1)
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f230])).

fof(f232,plain,
    ( ~ spl5_14
    | ~ spl5_16
    | spl5_27
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f195,f88,f230,f149,f143])).

fof(f88,plain,
    ( spl5_6
  <=> ! [X1] :
        ( v4_pre_topc(k10_relat_1(sK2,X1),sK0)
        | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_6 ),
    inference(resolution,[],[f89,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f89,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
        | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v4_pre_topc(k10_relat_1(sK2,X1),sK0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f224,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f188,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f188,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl5_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f214,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f191,f26])).

fof(f26,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f191,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl5_20
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f193,plain,
    ( spl5_1
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_15
    | ~ spl5_16
    | spl5_10 ),
    inference(avatar_split_clause,[],[f134,f124,f149,f146,f190,f187,f152,f44])).

fof(f44,plain,
    ( spl5_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f152,plain,
    ( spl5_17
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f146,plain,
    ( spl5_15
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f124,plain,
    ( spl5_10
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | spl5_10 ),
    inference(resolution,[],[f125,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f1])).

% (24653)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f1,axiom,(
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

fof(f125,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f192,plain,
    ( spl5_1
    | ~ spl5_17
    | ~ spl5_19
    | ~ spl5_20
    | ~ spl5_15
    | ~ spl5_16
    | spl5_9 ),
    inference(avatar_split_clause,[],[f135,f121,f149,f146,f190,f187,f152,f44])).

fof(f121,plain,
    ( spl5_9
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | spl5_9 ),
    inference(resolution,[],[f122,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f122,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f185,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f112,f117])).

fof(f117,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_2 ),
    inference(forward_demodulation,[],[f48,f24])).

fof(f24,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_2
  <=> v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f112,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_4
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f183,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl5_18 ),
    inference(resolution,[],[f156,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f23,f24])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f11])).

fof(f156,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f181,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f141,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f22,f24])).

fof(f22,plain,(
    v1_funct_2(sK3,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f141,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_13
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f177,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl5_17 ),
    inference(resolution,[],[f153,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f153,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f152])).

fof(f171,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl5_16 ),
    inference(resolution,[],[f150,f29])).

fof(f29,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f150,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f165,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl5_15 ),
    inference(resolution,[],[f147,f25])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f147,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f163,plain,
    ( ~ spl5_5
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | spl5_4
    | ~ spl5_17
    | ~ spl5_18
    | spl5_11 ),
    inference(avatar_split_clause,[],[f162,f128,f155,f152,f82,f149,f146,f143,f140,f85])).

fof(f85,plain,
    ( spl5_5
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f128,plain,
    ( spl5_11
  <=> m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f162,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_11 ),
    inference(resolution,[],[f129,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(X2)
      | m1_subset_1(sK4(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ),
    inference(resolution,[],[f66,f35])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(sK4(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(global_subsumption,[],[f57,f64])).

% (24651)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X2)
      | v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(sK4(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f34,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f129,plain,
    ( ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f128])).

fof(f161,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f144,f28])).

fof(f28,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f144,plain,
    ( ~ v2_pre_topc(sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f157,plain,
    ( ~ spl5_5
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | ~ spl5_16
    | spl5_4
    | ~ spl5_17
    | ~ spl5_18
    | spl5_12 ),
    inference(avatar_split_clause,[],[f138,f131,f155,f152,f82,f149,f146,f143,f140,f85])).

fof(f131,plain,
    ( spl5_12
  <=> v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f138,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_pre_topc(sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_12 ),
    inference(resolution,[],[f132,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK4(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X0)
      | ~ v2_pre_topc(X2)
      | v4_pre_topc(sK4(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0),X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ l1_pre_topc(X1)
      | v5_pre_topc(X0,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ),
    inference(resolution,[],[f67,f35])).

fof(f67,plain,(
    ! [X4,X5,X3] :
      ( ~ v4_pre_topc(sK4(X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4),g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
      | ~ l1_pre_topc(X5)
      | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ l1_pre_topc(X3)
      | ~ v1_funct_1(X4)
      | ~ v2_pre_topc(X3)
      | v4_pre_topc(sK4(X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4),X3) ) ),
    inference(global_subsumption,[],[f57,f65])).

fof(f65,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
      | ~ l1_pre_topc(X5)
      | v5_pre_topc(X4,X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ l1_pre_topc(X3)
      | ~ v4_pre_topc(sK4(X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4),g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ v2_pre_topc(X3)
      | v4_pre_topc(sK4(X5,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4),X3) ) ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f132,plain,
    ( ~ v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f119,f114,f108,f131,f128])).

fof(f114,plain,
    ( spl5_8
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f119,plain,
    ( ~ v4_pre_topc(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),sK1)
    | ~ m1_subset_1(sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_7
    | spl5_8 ),
    inference(resolution,[],[f109,f115])).

fof(f115,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f109,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f126,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f118,f108,f73,f124,f121])).

fof(f73,plain,
    ( spl5_3
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f118,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f109,f74])).

fof(f74,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f116,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f111,f114,f85,f82])).

fof(f111,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(global_subsumption,[],[f25,f31,f55,f56,f70])).

fof(f70,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),sK0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(superposition,[],[f36,f59])).

fof(f59,plain,(
    ! [X1] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(resolution,[],[f42,f56])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f110,plain,
    ( ~ spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f106,f108,f44])).

fof(f106,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(global_subsumption,[],[f25,f29,f31,f26,f27,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(superposition,[],[f33,f58])).

fof(f58,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f42,f27])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | ~ l1_pre_topc(X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl5_2
    | spl5_4 ),
    inference(resolution,[],[f83,f54])).

fof(f54,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f51,f24])).

fof(f51,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f83,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f97,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f91,f29])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_5 ),
    inference(resolution,[],[f86,f57])).

fof(f86,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f90,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f80,f88,f85,f82])).

fof(f80,plain,(
    ! [X1] :
      ( v4_pre_topc(k10_relat_1(sK2,X1),sK0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) ),
    inference(global_subsumption,[],[f25,f31,f55,f56,f78])).

fof(f78,plain,(
    ! [X1] :
      ( v4_pre_topc(k10_relat_1(sK2,X1),sK0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ l1_pre_topc(sK0)
      | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ) ),
    inference(superposition,[],[f33,f59])).

% (24655)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f75,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f71,f73,f44])).

fof(f71,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f25,f29,f31,f26,f27,f69])).

fof(f69,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(superposition,[],[f36,f58])).

fof(f52,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f19,f47,f44])).

fof(f19,plain,
    ( v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f20,f47,f44])).

fof(f20,plain,
    ( ~ v5_pre_topc(sK3,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
