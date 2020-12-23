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
% DateTime   : Thu Dec  3 13:20:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 129 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  234 ( 386 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f117,f119,f153,f181,f330])).

fof(f330,plain,(
    ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f68,f267,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f267,plain,
    ( ! [X0] : r1_tarski(k2_tarski(sK1,sK1),X0)
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f195,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f195,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_tarski(sK1,sK1))
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f180,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f180,plain,
    ( v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl4_13
  <=> v1_xboole_0(k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f68,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f181,plain,
    ( spl4_13
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f173,f140,f109,f178])).

fof(f109,plain,
    ( spl4_6
  <=> k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f140,plain,
    ( spl4_8
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f173,plain,
    ( v1_xboole_0(k2_tarski(sK1,sK1))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f142,f111])).

fof(f111,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f142,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f140])).

fof(f153,plain,
    ( spl4_8
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f152,f114,f88,f78,f73,f140])).

fof(f73,plain,
    ( spl4_1
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f78,plain,
    ( spl4_2
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f88,plain,
    ( spl4_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f114,plain,
    ( spl4_7
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f152,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f151,f90])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f151,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f150,f75])).

fof(f75,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f150,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f134,f80])).

fof(f80,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f134,plain,
    ( ~ v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f116,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f116,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f119,plain,
    ( spl4_6
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f118,f88,f83,f109])).

fof(f83,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f118,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f107,f90])).

fof(f107,plain,
    ( k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f85,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f57,f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f85,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f117,plain,
    ( spl4_7
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f104,f88,f83,f114])).

fof(f104,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_3
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f90,f85,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f91,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f44,f88])).

fof(f44,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f86,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f46,f78])).

fof(f46,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f47,f73])).

fof(f47,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (2468)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.49  % (2484)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.49  % (2468)Refutation not found, incomplete strategy% (2468)------------------------------
% 0.20/0.49  % (2468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2468)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (2468)Memory used [KB]: 10746
% 0.20/0.49  % (2468)Time elapsed: 0.077 s
% 0.20/0.49  % (2468)------------------------------
% 0.20/0.49  % (2468)------------------------------
% 0.20/0.50  % (2484)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f331,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f117,f119,f153,f181,f330])).
% 0.20/0.50  fof(f330,plain,(
% 0.20/0.50    ~spl4_13),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f324])).
% 0.20/0.50  fof(f324,plain,(
% 0.20/0.50    $false | ~spl4_13),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f68,f267,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k2_tarski(sK1,sK1),X0)) ) | ~spl4_13),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f195,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK1,sK1))) ) | ~spl4_13),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f180,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(rectify,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    v1_xboole_0(k2_tarski(sK1,sK1)) | ~spl4_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f178])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    spl4_13 <=> v1_xboole_0(k2_tarski(sK1,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f54,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    spl4_13 | ~spl4_6 | ~spl4_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f173,f140,f109,f178])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    spl4_6 <=> k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    spl4_8 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    v1_xboole_0(k2_tarski(sK1,sK1)) | (~spl4_6 | ~spl4_8)),
% 0.20/0.50    inference(backward_demodulation,[],[f142,f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | ~spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f109])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl4_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f140])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    spl4_8 | ~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f152,f114,f88,f78,f73,f140])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl4_1 <=> v1_zfmisc_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl4_2 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl4_4 <=> v1_xboole_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    spl4_7 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    v1_xboole_0(k6_domain_1(sK0,sK1)) | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f151,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0) | spl4_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f88])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0) | (~spl4_1 | ~spl4_2 | ~spl4_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f150,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    v1_zfmisc_1(sK0) | ~spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | (~spl4_2 | ~spl4_7)),
% 0.20/0.50    inference(subsumption_resolution,[],[f134,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f78])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    ~v1_subset_1(k6_domain_1(sK0,sK1),sK0) | v1_xboole_0(k6_domain_1(sK0,sK1)) | ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | ~spl4_7),
% 0.20/0.50    inference(resolution,[],[f116,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f114])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl4_6 | ~spl4_3 | spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f118,f88,f83,f109])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    spl4_3 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | (~spl4_3 | spl4_4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f107,f90])).
% 0.20/0.50  fof(f107,plain,(
% 0.20/0.50    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(sK0) | ~spl4_3),
% 0.20/0.50    inference(resolution,[],[f85,f69])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k2_tarski(X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f57,f49])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    m1_subset_1(sK1,sK0) | ~spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f83])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl4_7 | ~spl4_3 | spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f104,f88,f83,f114])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl4_3 | spl4_4)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f90,f85,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ~spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f44,f88])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f31,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.50    inference(negated_conjecture,[],[f15])).
% 0.20/0.50  fof(f15,conjecture,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f45,f83])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    m1_subset_1(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f46,f78])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f47,f73])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    v1_zfmisc_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (2484)------------------------------
% 0.20/0.50  % (2484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2484)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (2484)Memory used [KB]: 6396
% 0.20/0.50  % (2484)Time elapsed: 0.090 s
% 0.20/0.50  % (2484)------------------------------
% 0.20/0.50  % (2484)------------------------------
% 0.20/0.50  % (2458)Success in time 0.14 s
%------------------------------------------------------------------------------
