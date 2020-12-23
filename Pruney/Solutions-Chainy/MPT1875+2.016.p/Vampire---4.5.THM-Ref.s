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
% DateTime   : Thu Dec  3 13:21:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 182 expanded)
%              Number of leaves         :   16 (  53 expanded)
%              Depth                    :   22
%              Number of atoms          :  358 ( 811 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f316,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f199,f296,f315])).

fof(f315,plain,
    ( ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f60,f40,f77,f310,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X1,X3)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ m1_subset_1(X0,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f310,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f308,f284])).

fof(f284,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl4_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f308,plain,
    ( ~ l1_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f211,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

% (26235)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f211,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2 ),
    inference(resolution,[],[f206,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f206,plain,
    ( ! [X2] :
        ( v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2 ),
    inference(resolution,[],[f101,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f101,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_2
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f77,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f59])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f60,plain,(
    ! [X0] : sQ3_eqProxy(k2_subset_1(X0),X0) ),
    inference(equality_proxy_replacement,[],[f39,f59])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f296,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f293,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f293,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_7 ),
    inference(resolution,[],[f285,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f285,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f283])).

fof(f199,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f197,f100])).

fof(f100,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f197,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f195,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f195,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f190,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f190,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f186,f37])).

fof(f186,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f141,f38])).

fof(f38,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,
    ( ! [X3] :
        ( v2_tex_2(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f135,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f111,f104])).

fof(f104,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_3
  <=> r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f35,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tdlat_3(sK0)
        | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f109,f100])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tdlat_3(sK0)
      | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f107,f36])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tdlat_3(sK0)
      | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f87,f34])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X1)
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_tdlat_3(X1)
      | ~ r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | v2_tex_2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X0,X1)
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_tdlat_3(X1)
      | ~ r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X0,X1)
      | ~ r1_tarski(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_tdlat_3(X1)
      | ~ r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f42,f81])).

fof(f81,plain,(
    ! [X1] :
      ( v2_tex_2(u1_struct_0(X1),X1)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_tdlat_3(X1)
      | ~ r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f47,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | v2_tex_2(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f125,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f60,f40,f77,f115,f70])).

fof(f115,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f114,f100])).

fof(f114,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_3 ),
    inference(resolution,[],[f105,f46])).

fof(f105,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (26239)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (26249)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (26241)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (26249)Refutation not found, incomplete strategy% (26249)------------------------------
% 0.20/0.47  % (26249)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (26249)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (26249)Memory used [KB]: 6140
% 0.20/0.47  % (26249)Time elapsed: 0.008 s
% 0.20/0.47  % (26249)------------------------------
% 0.20/0.47  % (26249)------------------------------
% 0.20/0.47  % (26239)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (26247)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (26245)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (26238)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (26240)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (26251)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (26253)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.49  % (26248)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (26245)Refutation not found, incomplete strategy% (26245)------------------------------
% 0.20/0.49  % (26245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (26245)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (26245)Memory used [KB]: 10618
% 0.20/0.49  % (26245)Time elapsed: 0.076 s
% 0.20/0.49  % (26245)------------------------------
% 0.20/0.49  % (26245)------------------------------
% 0.20/0.49  % (26237)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (26237)Refutation not found, incomplete strategy% (26237)------------------------------
% 0.20/0.49  % (26237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (26243)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f316,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f125,f199,f296,f315])).
% 0.20/0.49  fof(f315,plain,(
% 0.20/0.49    ~spl4_2 | ~spl4_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f311])).
% 0.20/0.49  fof(f311,plain,(
% 0.20/0.49    $false | (~spl4_2 | ~spl4_7)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f60,f40,f77,f310,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X1,X3) | ~sQ3_eqProxy(X2,X3) | ~m1_subset_1(X0,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.20/0.49    inference(equality_proxy_axiom,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.20/0.49  fof(f310,plain,(
% 0.20/0.49    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_7)),
% 0.20/0.49    inference(subsumption_resolution,[],[f308,f284])).
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    l1_struct_0(sK0) | ~spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f283])).
% 0.20/0.49  fof(f283,plain,(
% 0.20/0.49    spl4_7 <=> l1_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f308,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 0.20/0.49    inference(resolution,[],[f211,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f26,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.49  % (26235)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_2),
% 0.20/0.49    inference(resolution,[],[f206,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    ( ! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_2),
% 0.20/0.49    inference(resolution,[],[f101,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl4_2 <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.20/0.49    inference(equality_proxy_axiom,[],[f59])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0] : (sQ3_eqProxy(k2_subset_1(X0),X0)) )),
% 0.20/0.49    inference(equality_proxy_replacement,[],[f39,f59])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.49  fof(f296,plain,(
% 0.20/0.49    spl4_7),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f295])).
% 0.20/0.49  fof(f295,plain,(
% 0.20/0.49    $false | spl4_7),
% 0.20/0.49    inference(subsumption_resolution,[],[f293,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | spl4_7),
% 0.20/0.49    inference(resolution,[],[f285,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.49  fof(f285,plain,(
% 0.20/0.49    ~l1_struct_0(sK0) | spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f283])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl4_2 | ~spl4_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f198])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    $false | (spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f197,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f99])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f195,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(resolution,[],[f190,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ~r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f186,f37])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(resolution,[],[f141,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ~v2_tex_2(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X3] : (v2_tex_2(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(resolution,[],[f135,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(equality_resolution,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.49    inference(rectify,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (spl4_2 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f111,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl4_3 <=> r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | spl4_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    v1_tdlat_3(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | spl4_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f109,f100])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f107,f36])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0) | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f87,f34])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X1) | ~r1_tarski(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) | ~v1_tdlat_3(X1) | ~r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) | v2_tex_2(X0,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f86,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_tex_2(X0,X1) | ~r1_tarski(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) | ~v1_tdlat_3(X1) | ~r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_tex_2(X0,X1) | ~r1_tarski(X0,u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) | ~v1_tdlat_3(X1) | ~r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.49    inference(resolution,[],[f42,f81])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X1] : (v2_tex_2(u1_struct_0(X1),X1) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(X1))) | ~v1_tdlat_3(X1) | ~r2_hidden(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.20/0.49    inference(resolution,[],[f47,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | v2_tex_2(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_tex_2(X1,X0) | v2_tex_2(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl4_2 | spl4_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f122])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    $false | (spl4_2 | spl4_3)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f60,f40,f77,f115,f70])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_2 | spl4_3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f114,f100])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | spl4_3),
% 0.20/0.50    inference(resolution,[],[f105,f46])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f103])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (26239)------------------------------
% 0.20/0.50  % (26239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26239)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (26239)Memory used [KB]: 6268
% 0.20/0.50  % (26239)Time elapsed: 0.060 s
% 0.20/0.50  % (26239)------------------------------
% 0.20/0.50  % (26239)------------------------------
% 0.20/0.50  % (26237)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (26237)Memory used [KB]: 10618
% 0.20/0.50  % (26237)Time elapsed: 0.078 s
% 0.20/0.50  % (26237)------------------------------
% 0.20/0.50  % (26237)------------------------------
% 0.20/0.50  % (26233)Success in time 0.137 s
%------------------------------------------------------------------------------
