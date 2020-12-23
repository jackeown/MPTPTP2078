%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 201 expanded)
%              Number of leaves         :   24 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  351 (1120 expanded)
%              Number of equality atoms :   46 ( 167 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f105,f110,f122,f143,f145,f255,f266,f269,f279,f282])).

% (17204)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% (17199)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f282,plain,
    ( ~ spl5_2
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(trivial_inequality_removal,[],[f280])).

fof(f280,plain,
    ( k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(superposition,[],[f75,f278])).

fof(f278,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl5_24
  <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f75,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f41,f73])).

fof(f73,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_2
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f41,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).

fof(f279,plain,
    ( ~ spl5_7
    | spl5_24
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f273,f264,f276,f107])).

fof(f107,plain,
    ( spl5_7
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f264,plain,
    ( spl5_23
  <=> ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f273,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_23 ),
    inference(resolution,[],[f270,f40])).

fof(f40,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0)))
        | ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_23 ),
    inference(resolution,[],[f265,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f55,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f42])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f264])).

fof(f269,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl5_22 ),
    inference(resolution,[],[f262,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f262,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl5_22
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f266,plain,
    ( ~ spl5_22
    | spl5_23
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f256,f253,f264,f260])).

fof(f253,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f256,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_21 ),
    inference(resolution,[],[f254,f38])).

fof(f38,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X1,sK0)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl5_8
    | ~ spl5_9
    | spl5_21 ),
    inference(avatar_split_clause,[],[f251,f253,f135,f131])).

fof(f131,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f135,plain,
    ( spl5_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).

fof(f145,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl5_8 ),
    inference(resolution,[],[f133,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f133,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f143,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f137,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f122,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f119,f40])).

fof(f119,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f117,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f117,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f111,f37])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f69,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f110,plain,
    ( spl5_1
    | ~ spl5_5
    | spl5_7
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f77,f71,f107,f96,f67])).

fof(f96,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f77,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(superposition,[],[f52,f73])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f105,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f98,f39])).

fof(f39,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f74,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f65,f71,f67])).

fof(f65,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (17203)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (17197)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (17207)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (17208)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (17197)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f74,f105,f110,f122,f143,f145,f255,f266,f269,f279,f282])).
% 0.21/0.48  % (17204)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (17199)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    ~spl5_2 | ~spl5_24),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f281])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    $false | (~spl5_2 | ~spl5_24)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f280])).
% 0.21/0.48  fof(f280,plain,(
% 0.21/0.48    k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2) | (~spl5_2 | ~spl5_24)),
% 0.21/0.48    inference(superposition,[],[f75,f278])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl5_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f276])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    spl5_24 <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl5_2),
% 0.21/0.48    inference(backward_demodulation,[],[f41,f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl5_2 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    ~spl5_7 | spl5_24 | ~spl5_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f273,f264,f276,f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl5_7 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    spl5_23 <=> ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_23),
% 0.21/0.48    inference(resolution,[],[f270,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    r2_hidden(sK2,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0))) | ~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_23),
% 0.21/0.48    inference(resolution,[],[f265,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f55,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f50,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) ) | ~spl5_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f264])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    spl5_22),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f267])).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    $false | spl5_22),
% 0.21/0.49    inference(resolution,[],[f262,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f260])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    spl5_22 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ~spl5_22 | spl5_23 | ~spl5_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f256,f253,f264,f260])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    spl5_21 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_21),
% 0.21/0.49    inference(resolution,[],[f254,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f253])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    spl5_8 | ~spl5_9 | spl5_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f251,f253,f135,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl5_8 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl5_9 <=> v2_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f44,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ~spl5_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    $false | ~spl5_8),
% 0.21/0.49    inference(resolution,[],[f133,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f131])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl5_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    $false | spl5_9),
% 0.21/0.49    inference(resolution,[],[f137,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | spl5_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f135])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    ~spl5_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    $false | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f119,f40])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f117,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(rectify,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f111,f37])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) ) | ~spl5_1),
% 0.21/0.49    inference(resolution,[],[f69,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl5_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl5_1 | ~spl5_5 | spl5_7 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f77,f71,f107,f96,f67])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl5_5 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl5_2),
% 0.21/0.49    inference(superposition,[],[f52,f73])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl5_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    $false | spl5_5),
% 0.21/0.49    inference(resolution,[],[f98,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,u1_struct_0(sK0)) | spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl5_1 | spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f65,f71,f67])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f56,f39])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f51,f42])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17197)------------------------------
% 0.21/0.49  % (17197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17197)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17197)Memory used [KB]: 6268
% 0.21/0.49  % (17197)Time elapsed: 0.070 s
% 0.21/0.49  % (17197)------------------------------
% 0.21/0.49  % (17197)------------------------------
% 0.21/0.49  % (17194)Success in time 0.129 s
%------------------------------------------------------------------------------
