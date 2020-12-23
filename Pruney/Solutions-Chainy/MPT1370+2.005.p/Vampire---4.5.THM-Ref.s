%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 238 expanded)
%              Number of leaves         :   13 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  402 (3087 expanded)
%              Number of equality atoms :   17 ( 206 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f60,f77,f83])).

fof(f83,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f81,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    & v4_pre_topc(sK3,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & v5_pre_topc(sK2,sK0,sK1)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & v8_pre_topc(sK1)
    & v1_compts_1(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f19,f18,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v5_pre_topc(X2,X0,X1)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,sK0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & v5_pre_topc(X2,sK0,X1)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                & v4_pre_topc(X3,sK0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & v5_pre_topc(X2,sK0,X1)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & v8_pre_topc(X1)
            & v1_compts_1(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
              & v4_pre_topc(X3,sK0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v5_pre_topc(X2,sK0,sK1)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & v8_pre_topc(sK1)
          & v1_compts_1(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (6640)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% (6655)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
fof(f18,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
            & v4_pre_topc(X3,sK0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v5_pre_topc(X2,sK0,sK1)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & v8_pre_topc(sK1)
        & v1_compts_1(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
          & v4_pre_topc(X3,sK0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v5_pre_topc(sK2,sK0,sK1)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & v8_pre_topc(sK1)
      & v1_compts_1(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
        & v4_pre_topc(X3,sK0)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
      & v4_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                       => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

fof(f81,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f80,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f79,f29])).

fof(f29,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,
    ( ~ v1_compts_1(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f34,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,
    ( ~ v4_pre_topc(sK3,sK0)
    | ~ v1_compts_1(sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_3 ),
    inference(resolution,[],[f76,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

fof(f76,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_3
  <=> v2_compts_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f77,plain,
    ( ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f72,f54,f74])).

fof(f54,plain,
    ( spl5_2
  <=> v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f72,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f71,f33])).

fof(f71,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_2 ),
    inference(resolution,[],[f70,f56])).

fof(f56,plain,
    ( ~ v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f70,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f69,f41])).

fof(f41,plain,(
    sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(equality_proxy_replacement,[],[f31,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f31,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ) ),
    inference(subsumption_resolution,[],[f68,f22])).

fof(f68,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ) ),
    inference(subsumption_resolution,[],[f67,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ) ),
    inference(subsumption_resolution,[],[f66,f25])).

fof(f25,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ) ),
    inference(subsumption_resolution,[],[f65,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ) ),
    inference(subsumption_resolution,[],[f64,f32])).

fof(f32,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ) ),
    inference(resolution,[],[f63,f27])).

fof(f27,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v5_pre_topc(sK2,X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2),X1)
      | ~ v2_compts_1(X2,X0)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ sQ4_eqProxy(k2_struct_0(X1),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)) ) ),
    inference(resolution,[],[f62,f26])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X2)
      | ~ v5_pre_topc(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v2_compts_1(X0,X1)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ sQ4_eqProxy(k2_struct_0(X2),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)) ) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f40])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sQ4_eqProxy(k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3),k2_struct_0(X2))
      | ~ v2_compts_1(X1,X0)
      | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
      | ~ v5_pre_topc(X3,X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f37,f40])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
      | ~ v2_compts_1(X1,X0)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
      | ~ v5_pre_topc(X3,X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ( ( v2_compts_1(X1,X0)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v5_pre_topc(X3,X0,X2) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_compts_1)).

fof(f60,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_1 ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f52,plain,
    ( ~ m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_1
  <=> m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f57,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f54,f50])).

fof(f48,plain,
    ( ~ v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( v4_pre_topc(X0,sK1)
      | ~ v2_compts_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f46,f24])).

fof(f24,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

% (6653)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f46,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK1)
      | v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f45,f25])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK1)
      | v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:20:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (6638)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (6656)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (6639)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (6648)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (6635)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (6654)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (6656)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f57,f60,f77,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl5_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    $false | spl5_3),
% 0.21/0.51    inference(subsumption_resolution,[],[f81,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    (((~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) & v4_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(sK2,sK0,sK1) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f19,f18,f17,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,X1) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,X1) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,sK1) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.52  % (6640)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (6655)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,sK1) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(sK2,sK0,sK1) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) & v4_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f80,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f79,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    v1_compts_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~v1_compts_1(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v4_pre_topc(sK3,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ~v4_pre_topc(sK3,sK0) | ~v1_compts_1(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_3),
% 0.21/0.52    inference(resolution,[],[f76,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ~v2_compts_1(sK3,sK0) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl5_3 <=> v2_compts_1(sK3,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ~spl5_3 | spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f72,f54,f74])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl5_2 <=> v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ~v2_compts_1(sK3,sK0) | spl5_2),
% 0.21/0.52    inference(subsumption_resolution,[],[f71,f33])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~v2_compts_1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_2),
% 0.21/0.52    inference(resolution,[],[f70,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) | spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0] : (v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f31,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.52    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f68,f22])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f67,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ~v2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    l1_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f65,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f64,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (~v5_pre_topc(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~sQ4_eqProxy(k2_struct_0(sK1),k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) )),
% 0.21/0.52    inference(resolution,[],[f63,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v5_pre_topc(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X2),X1) | ~v2_compts_1(X2,X0) | ~l1_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~sQ4_eqProxy(k2_struct_0(X1),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2))) )),
% 0.21/0.52    inference(resolution,[],[f62,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X0),X2) | ~v5_pre_topc(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v2_compts_1(X0,X1) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~sQ4_eqProxy(k2_struct_0(X2),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3))) )),
% 0.21/0.52    inference(resolution,[],[f42,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.52    inference(equality_proxy_axiom,[],[f40])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~sQ4_eqProxy(k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3),k2_struct_0(X2)) | ~v2_compts_1(X1,X0) | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | ~v5_pre_topc(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(equality_proxy_replacement,[],[f37,f40])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | ~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | ~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | (~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)) => ((v2_compts_1(X1,X0) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2) & v5_pre_topc(X3,X0,X2)) => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_compts_1)).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    spl5_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    $false | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f58,f28])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f52,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    spl5_1 <=> m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f48,f54,f50])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ~v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) | ~m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.21/0.52    inference(resolution,[],[f47,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (v4_pre_topc(X0,sK1) | ~v2_compts_1(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f46,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    v2_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  % (6653)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_compts_1(X0,sK1) | v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f45,f25])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_compts_1(X0,sK1) | v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.52    inference(resolution,[],[f38,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    v8_pre_topc(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v8_pre_topc(X0) | ~v2_compts_1(X1,X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (6656)------------------------------
% 0.21/0.52  % (6656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6656)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (6656)Memory used [KB]: 10618
% 0.21/0.52  % (6656)Time elapsed: 0.059 s
% 0.21/0.52  % (6656)------------------------------
% 0.21/0.52  % (6656)------------------------------
% 0.21/0.52  % (6651)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (6646)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (6637)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % (6634)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (6632)Success in time 0.154 s
%------------------------------------------------------------------------------
