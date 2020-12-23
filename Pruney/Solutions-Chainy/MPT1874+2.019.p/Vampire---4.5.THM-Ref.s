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
% DateTime   : Thu Dec  3 13:21:24 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 213 expanded)
%              Number of leaves         :   23 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  342 (1130 expanded)
%              Number of equality atoms :   46 ( 170 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f203,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f85,f128,f144,f146,f174,f184,f186,f197,f199,f202])).

fof(f202,plain,
    ( ~ spl4_10
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,
    ( k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2)
    | ~ spl4_10
    | ~ spl4_22 ),
    inference(superposition,[],[f129,f196])).

fof(f196,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_22
  <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f129,plain,
    ( k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl4_10 ),
    inference(backward_demodulation,[],[f37,f127])).

fof(f127,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_10
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f37,plain,(
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

fof(f199,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl4_21 ),
    inference(resolution,[],[f192,f36])).

fof(f36,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f192,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl4_21
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f197,plain,
    ( ~ spl4_21
    | spl4_22
    | ~ spl4_1
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f188,f182,f58,f194,f190])).

fof(f58,plain,
    ( spl4_1
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f182,plain,
    ( spl4_20
  <=> ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f188,plain,
    ( k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ r2_hidden(sK2,sK1)
    | ~ spl4_1
    | ~ spl4_20 ),
    inference(resolution,[],[f187,f86])).

fof(f86,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f60,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) ) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f60,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_20 ),
    inference(resolution,[],[f183,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f183,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f186,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl4_19 ),
    inference(resolution,[],[f180,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f180,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f178])).

% (309)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f178,plain,
    ( spl4_19
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f184,plain,
    ( ~ spl4_19
    | spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f175,f172,f182,f178])).

fof(f172,plain,
    ( spl4_18
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

% (315)Refutation not found, incomplete strategy% (315)------------------------------
% (315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (315)Termination reason: Refutation not found, incomplete strategy

% (315)Memory used [KB]: 10618
% (315)Time elapsed: 0.080 s
% (315)------------------------------
% (315)------------------------------
fof(f175,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_18 ),
    inference(resolution,[],[f173,f34])).

fof(f34,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X1,sK0)
        | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( spl4_11
    | ~ spl4_12
    | spl4_18 ),
    inference(avatar_split_clause,[],[f170,f172,f136,f132])).

fof(f132,plain,
    ( spl4_11
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f136,plain,
    ( spl4_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
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

fof(f146,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl4_11 ),
    inference(resolution,[],[f134,f30])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f134,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f144,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl4_12 ),
    inference(resolution,[],[f138,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f138,plain,
    ( ~ v2_pre_topc(sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f128,plain,
    ( spl4_2
    | spl4_10 ),
    inference(avatar_split_clause,[],[f120,f125,f62])).

fof(f62,plain,
    ( spl4_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f120,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f52,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f47,f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f85,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl4_2 ),
    inference(resolution,[],[f81,f50])).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f38,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f81,plain,
    ( v1_xboole_0(k2_tarski(sK2,sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f79,f68])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f67,f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f67,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f66,f33])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f64,f40])).

fof(f64,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f79,plain,(
    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f51,f36])).

fof(f65,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f55,f62,f58])).

fof(f55,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f46,f35])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 15:25:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.23/0.51  % (311)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.51  % (307)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.52  % (308)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.52  % (306)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.52  % (321)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.52  % (314)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.52  % (319)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.52  % (306)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % (316)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.52  % (315)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.52  % (317)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.52  % (313)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f203,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(avatar_sat_refutation,[],[f65,f85,f128,f144,f146,f174,f184,f186,f197,f199,f202])).
% 0.23/0.52  fof(f202,plain,(
% 0.23/0.52    ~spl4_10 | ~spl4_22),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f201])).
% 0.23/0.52  fof(f201,plain,(
% 0.23/0.52    $false | (~spl4_10 | ~spl4_22)),
% 0.23/0.52    inference(trivial_inequality_removal,[],[f200])).
% 0.23/0.52  fof(f200,plain,(
% 0.23/0.52    k2_tarski(sK2,sK2) != k2_tarski(sK2,sK2) | (~spl4_10 | ~spl4_22)),
% 0.23/0.52    inference(superposition,[],[f129,f196])).
% 0.23/0.52  fof(f196,plain,(
% 0.23/0.52    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl4_22),
% 0.23/0.52    inference(avatar_component_clause,[],[f194])).
% 0.23/0.52  fof(f194,plain,(
% 0.23/0.52    spl4_22 <=> k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.23/0.52  fof(f129,plain,(
% 0.23/0.52    k2_tarski(sK2,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~spl4_10),
% 0.23/0.52    inference(backward_demodulation,[],[f37,f127])).
% 0.23/0.52  fof(f127,plain,(
% 0.23/0.52    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl4_10),
% 0.23/0.52    inference(avatar_component_clause,[],[f125])).
% 0.23/0.52  fof(f125,plain,(
% 0.23/0.52    spl4_10 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.23/0.52  fof(f37,plain,(
% 0.23/0.52    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.23/0.52    inference(cnf_transformation,[],[f24])).
% 0.23/0.52  fof(f24,plain,(
% 0.23/0.52    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f23,f22,f21])).
% 0.23/0.52  fof(f21,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f22,plain,(
% 0.23/0.52    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f23,plain,(
% 0.23/0.52    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.23/0.52    introduced(choice_axiom,[])).
% 0.23/0.52  fof(f12,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.52    inference(flattening,[],[f11])).
% 0.23/0.52  fof(f11,plain,(
% 0.23/0.52    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.52    inference(ennf_transformation,[],[f10])).
% 0.23/0.52  fof(f10,negated_conjecture,(
% 0.23/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.23/0.52    inference(negated_conjecture,[],[f9])).
% 0.23/0.52  fof(f9,conjecture,(
% 0.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_tex_2)).
% 0.23/0.52  fof(f199,plain,(
% 0.23/0.52    spl4_21),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f198])).
% 0.23/0.52  fof(f198,plain,(
% 0.23/0.52    $false | spl4_21),
% 0.23/0.52    inference(resolution,[],[f192,f36])).
% 0.23/0.52  fof(f36,plain,(
% 0.23/0.52    r2_hidden(sK2,sK1)),
% 0.23/0.52    inference(cnf_transformation,[],[f24])).
% 0.23/0.52  fof(f192,plain,(
% 0.23/0.52    ~r2_hidden(sK2,sK1) | spl4_21),
% 0.23/0.52    inference(avatar_component_clause,[],[f190])).
% 0.23/0.52  fof(f190,plain,(
% 0.23/0.52    spl4_21 <=> r2_hidden(sK2,sK1)),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.23/0.52  fof(f197,plain,(
% 0.23/0.52    ~spl4_21 | spl4_22 | ~spl4_1 | ~spl4_20),
% 0.23/0.52    inference(avatar_split_clause,[],[f188,f182,f58,f194,f190])).
% 0.23/0.52  fof(f58,plain,(
% 0.23/0.52    spl4_1 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.52  fof(f182,plain,(
% 0.23/0.52    spl4_20 <=> ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.23/0.52  fof(f188,plain,(
% 0.23/0.52    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | ~r2_hidden(sK2,sK1) | (~spl4_1 | ~spl4_20)),
% 0.23/0.52    inference(resolution,[],[f187,f86])).
% 0.23/0.52  fof(f86,plain,(
% 0.23/0.52    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_1),
% 0.23/0.52    inference(resolution,[],[f60,f51])).
% 0.23/0.52  fof(f51,plain,(
% 0.23/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))) )),
% 0.23/0.52    inference(definition_unfolding,[],[f45,f39])).
% 0.23/0.52  fof(f39,plain,(
% 0.23/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.52  fof(f45,plain,(
% 0.23/0.52    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f16])).
% 0.23/0.52  fof(f16,plain,(
% 0.23/0.52    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.23/0.52    inference(ennf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.23/0.53  fof(f60,plain,(
% 0.23/0.53    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl4_1),
% 0.23/0.53    inference(avatar_component_clause,[],[f58])).
% 0.23/0.53  fof(f187,plain,(
% 0.23/0.53    ( ! [X0] : (~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tarski(X0,X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k2_tarski(X0,X0))) | ~r2_hidden(X0,sK1)) ) | ~spl4_20),
% 0.23/0.53    inference(resolution,[],[f183,f53])).
% 0.23/0.53  fof(f53,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f49,f39])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f29])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.23/0.53    inference(nnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.23/0.53  fof(f183,plain,(
% 0.23/0.53    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) ) | ~spl4_20),
% 0.23/0.53    inference(avatar_component_clause,[],[f182])).
% 0.23/0.53  fof(f186,plain,(
% 0.23/0.53    spl4_19),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f185])).
% 0.23/0.53  fof(f185,plain,(
% 0.23/0.53    $false | spl4_19),
% 0.23/0.53    inference(resolution,[],[f180,f33])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f180,plain,(
% 0.23/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_19),
% 0.23/0.53    inference(avatar_component_clause,[],[f178])).
% 0.23/0.53  % (309)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.53  fof(f178,plain,(
% 0.23/0.53    spl4_19 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.23/0.53  fof(f184,plain,(
% 0.23/0.53    ~spl4_19 | spl4_20 | ~spl4_18),
% 0.23/0.53    inference(avatar_split_clause,[],[f175,f172,f182,f178])).
% 0.23/0.53  fof(f172,plain,(
% 0.23/0.53    spl4_18 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.23/0.53  % (315)Refutation not found, incomplete strategy% (315)------------------------------
% 0.23/0.53  % (315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (315)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (315)Memory used [KB]: 10618
% 0.23/0.53  % (315)Time elapsed: 0.080 s
% 0.23/0.53  % (315)------------------------------
% 0.23/0.53  % (315)------------------------------
% 0.23/0.53  fof(f175,plain,(
% 0.23/0.53    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_18),
% 0.23/0.53    inference(resolution,[],[f173,f34])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    v2_tex_2(sK1,sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f173,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_18),
% 0.23/0.53    inference(avatar_component_clause,[],[f172])).
% 0.23/0.53  fof(f174,plain,(
% 0.23/0.53    spl4_11 | ~spl4_12 | spl4_18),
% 0.23/0.53    inference(avatar_split_clause,[],[f170,f172,f136,f132])).
% 0.23/0.53  fof(f132,plain,(
% 0.23/0.53    spl4_11 <=> v2_struct_0(sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.23/0.53  fof(f136,plain,(
% 0.23/0.53    spl4_12 <=> v2_pre_topc(sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.23/0.53  fof(f170,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.23/0.53    inference(resolution,[],[f41,f32])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    l1_pre_topc(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f28])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.53    inference(rectify,[],[f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.53    inference(nnf_transformation,[],[f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.23/0.53    inference(flattening,[],[f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tex_2)).
% 0.23/0.53  fof(f146,plain,(
% 0.23/0.53    ~spl4_11),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f145])).
% 0.23/0.53  fof(f145,plain,(
% 0.23/0.53    $false | ~spl4_11),
% 0.23/0.53    inference(resolution,[],[f134,f30])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    ~v2_struct_0(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f134,plain,(
% 0.23/0.53    v2_struct_0(sK0) | ~spl4_11),
% 0.23/0.53    inference(avatar_component_clause,[],[f132])).
% 0.23/0.53  fof(f144,plain,(
% 0.23/0.53    spl4_12),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f143])).
% 0.23/0.53  fof(f143,plain,(
% 0.23/0.53    $false | spl4_12),
% 0.23/0.53    inference(resolution,[],[f138,f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    v2_pre_topc(sK0)),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f138,plain,(
% 0.23/0.53    ~v2_pre_topc(sK0) | spl4_12),
% 0.23/0.53    inference(avatar_component_clause,[],[f136])).
% 0.23/0.53  fof(f128,plain,(
% 0.23/0.53    spl4_2 | spl4_10),
% 0.23/0.53    inference(avatar_split_clause,[],[f120,f125,f62])).
% 0.23/0.53  fof(f62,plain,(
% 0.23/0.53    spl4_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.53  fof(f120,plain,(
% 0.23/0.53    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0))),
% 0.23/0.53    inference(resolution,[],[f52,f35])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f47,f39])).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f20])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.23/0.53    inference(flattening,[],[f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.23/0.53    inference(ennf_transformation,[],[f7])).
% 0.23/0.53  fof(f7,axiom,(
% 0.23/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.23/0.53  fof(f85,plain,(
% 0.23/0.53    ~spl4_2),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f83])).
% 0.23/0.53  fof(f83,plain,(
% 0.23/0.53    $false | ~spl4_2),
% 0.23/0.53    inference(resolution,[],[f81,f50])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f38,f39])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.23/0.53  fof(f81,plain,(
% 0.23/0.53    v1_xboole_0(k2_tarski(sK2,sK2)) | ~spl4_2),
% 0.23/0.53    inference(resolution,[],[f79,f68])).
% 0.23/0.53  fof(f68,plain,(
% 0.23/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.23/0.53    inference(resolution,[],[f67,f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f13])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.23/0.53  fof(f67,plain,(
% 0.23/0.53    v1_xboole_0(sK1) | ~spl4_2),
% 0.23/0.53    inference(resolution,[],[f66,f33])).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.23/0.53    inference(resolution,[],[f64,f40])).
% 0.23/0.53  fof(f64,plain,(
% 0.23/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_2),
% 0.23/0.53    inference(avatar_component_clause,[],[f62])).
% 0.23/0.53  fof(f79,plain,(
% 0.23/0.53    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))),
% 0.23/0.53    inference(resolution,[],[f51,f36])).
% 0.23/0.53  fof(f65,plain,(
% 0.23/0.53    spl4_1 | spl4_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f55,f62,f58])).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2,u1_struct_0(sK0))),
% 0.23/0.53    inference(resolution,[],[f46,f35])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.53    inference(flattening,[],[f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (306)------------------------------
% 0.23/0.53  % (306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (306)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (306)Memory used [KB]: 6140
% 0.23/0.53  % (306)Time elapsed: 0.069 s
% 0.23/0.53  % (306)------------------------------
% 0.23/0.53  % (306)------------------------------
% 0.23/0.53  % (303)Success in time 0.16 s
%------------------------------------------------------------------------------
