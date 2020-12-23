%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:19 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 131 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  283 ( 429 expanded)
%              Number of equality atoms :   73 (  76 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f129,f140,f145,f187])).

fof(f187,plain,
    ( ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f183,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f183,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f161,f169])).

fof(f169,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f89,f144,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f144,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_9
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f89,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f161,plain,
    ( ~ m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(superposition,[],[f101,f139])).

fof(f139,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_8
  <=> k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f101,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_enumset1(X0,X0,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f68,f89,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f68,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f51,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

% (30503)Termination reason: Refutation not found, incomplete strategy
fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

% (30503)Memory used [KB]: 10618
fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

% (30503)Time elapsed: 0.136 s
fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

% (30503)------------------------------
% (30503)------------------------------
fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f145,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f130,f126,f92,f77,f142])).

fof(f77,plain,
    ( spl3_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,
    ( spl3_5
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f126,plain,
    ( spl3_7
  <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f130,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f79,f94,f128,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f44,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f128,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f94,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f79,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f140,plain,
    ( spl3_8
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f115,f82,f72,f137])).

fof(f72,plain,
    ( spl3_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f115,plain,
    ( k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f74,f84,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f84,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f74,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f129,plain,
    ( spl3_7
    | spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f110,f82,f72,f126])).

fof(f110,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_1
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f74,f84,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f95,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f38,f92])).

fof(f38,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f29,f28])).

% (30496)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f28,plain,
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

fof(f29,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

% (30493)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f90,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f87])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f85,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f82])).

fof(f37,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:51:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (30503)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (30510)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.45/0.55  % (30518)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.45/0.55  % (30520)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.45/0.56  % (30504)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.45/0.56  % (30511)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.56  % (30503)Refutation not found, incomplete strategy% (30503)------------------------------
% 1.45/0.56  % (30503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (30511)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.56  % (30520)Refutation not found, incomplete strategy% (30520)------------------------------
% 1.45/0.56  % (30520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (30492)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.45/0.56  % (30520)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (30520)Memory used [KB]: 1663
% 1.45/0.56  % (30520)Time elapsed: 0.133 s
% 1.45/0.56  % (30520)------------------------------
% 1.45/0.56  % (30520)------------------------------
% 1.45/0.57  % (30492)Refutation not found, incomplete strategy% (30492)------------------------------
% 1.45/0.57  % (30492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (30492)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (30492)Memory used [KB]: 1663
% 1.45/0.57  % (30492)Time elapsed: 0.144 s
% 1.45/0.57  % (30492)------------------------------
% 1.45/0.57  % (30492)------------------------------
% 1.45/0.57  % SZS output start Proof for theBenchmark
% 1.45/0.57  fof(f195,plain,(
% 1.45/0.57    $false),
% 1.45/0.57    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f129,f140,f145,f187])).
% 1.45/0.57  fof(f187,plain,(
% 1.45/0.57    ~spl3_4 | ~spl3_8 | ~spl3_9),
% 1.45/0.57    inference(avatar_contradiction_clause,[],[f186])).
% 1.45/0.57  fof(f186,plain,(
% 1.45/0.57    $false | (~spl3_4 | ~spl3_8 | ~spl3_9)),
% 1.45/0.57    inference(subsumption_resolution,[],[f183,f41])).
% 1.45/0.57  fof(f41,plain,(
% 1.45/0.57    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.45/0.57    inference(cnf_transformation,[],[f6])).
% 1.45/0.57  fof(f6,axiom,(
% 1.45/0.57    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.45/0.57  fof(f183,plain,(
% 1.45/0.57    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_4 | ~spl3_8 | ~spl3_9)),
% 1.45/0.57    inference(backward_demodulation,[],[f161,f169])).
% 1.45/0.57  fof(f169,plain,(
% 1.45/0.57    k1_xboole_0 = k6_domain_1(sK0,sK1) | (~spl3_4 | ~spl3_9)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f89,f144,f48])).
% 1.45/0.57  fof(f48,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f24])).
% 1.45/0.57  fof(f24,plain,(
% 1.45/0.57    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f2])).
% 1.45/0.57  fof(f2,axiom,(
% 1.45/0.57    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.45/0.57  fof(f144,plain,(
% 1.45/0.57    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl3_9),
% 1.45/0.57    inference(avatar_component_clause,[],[f142])).
% 1.45/0.57  fof(f142,plain,(
% 1.45/0.57    spl3_9 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.45/0.57  fof(f89,plain,(
% 1.45/0.57    v1_xboole_0(k1_xboole_0) | ~spl3_4),
% 1.45/0.57    inference(avatar_component_clause,[],[f87])).
% 1.45/0.57  fof(f87,plain,(
% 1.45/0.57    spl3_4 <=> v1_xboole_0(k1_xboole_0)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.45/0.57  fof(f161,plain,(
% 1.45/0.57    ~m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl3_4 | ~spl3_8)),
% 1.45/0.57    inference(superposition,[],[f101,f139])).
% 1.45/0.57  fof(f139,plain,(
% 1.45/0.57    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | ~spl3_8),
% 1.45/0.57    inference(avatar_component_clause,[],[f137])).
% 1.45/0.57  fof(f137,plain,(
% 1.45/0.57    spl3_8 <=> k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.45/0.57  fof(f101,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_subset_1(k1_enumset1(X0,X0,X1),k1_zfmisc_1(k1_xboole_0))) ) | ~spl3_4),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f68,f89,f56])).
% 1.45/0.57  fof(f56,plain,(
% 1.45/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f27])).
% 1.45/0.57  fof(f27,plain,(
% 1.45/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.45/0.57    inference(ennf_transformation,[],[f9])).
% 1.45/0.57  fof(f9,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.45/0.57  fof(f68,plain,(
% 1.45/0.57    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 1.45/0.57    inference(equality_resolution,[],[f67])).
% 1.45/0.57  fof(f67,plain,(
% 1.45/0.57    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 1.45/0.57    inference(equality_resolution,[],[f63])).
% 1.45/0.57  fof(f63,plain,(
% 1.45/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 1.45/0.57    inference(definition_unfolding,[],[f51,f45])).
% 1.45/0.57  fof(f45,plain,(
% 1.45/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f5])).
% 1.45/0.57  fof(f5,axiom,(
% 1.45/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.57  fof(f51,plain,(
% 1.45/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.45/0.57    inference(cnf_transformation,[],[f35])).
% 1.45/0.57  % (30503)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  fof(f35,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 1.45/0.57  
% 1.45/0.57  fof(f34,plain,(
% 1.45/0.57    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  % (30503)Memory used [KB]: 10618
% 1.45/0.57  fof(f33,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.57    inference(rectify,[],[f32])).
% 1.45/0.57  % (30503)Time elapsed: 0.136 s
% 1.45/0.57  fof(f32,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.57    inference(flattening,[],[f31])).
% 1.45/0.57  % (30503)------------------------------
% 1.45/0.57  % (30503)------------------------------
% 1.45/0.57  fof(f31,plain,(
% 1.45/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.45/0.57    inference(nnf_transformation,[],[f3])).
% 1.45/0.57  fof(f3,axiom,(
% 1.45/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.45/0.57  fof(f145,plain,(
% 1.45/0.57    spl3_9 | ~spl3_2 | ~spl3_5 | ~spl3_7),
% 1.45/0.57    inference(avatar_split_clause,[],[f130,f126,f92,f77,f142])).
% 1.45/0.57  fof(f77,plain,(
% 1.45/0.57    spl3_2 <=> v1_zfmisc_1(sK0)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.45/0.57  fof(f92,plain,(
% 1.45/0.57    spl3_5 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.45/0.57  fof(f126,plain,(
% 1.45/0.57    spl3_7 <=> m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.45/0.57  fof(f130,plain,(
% 1.45/0.57    v1_xboole_0(k6_domain_1(sK0,sK1)) | (~spl3_2 | ~spl3_5 | ~spl3_7)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f79,f94,f128,f70])).
% 1.45/0.57  fof(f70,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 1.45/0.57    inference(subsumption_resolution,[],[f44,f43])).
% 1.45/0.57  fof(f43,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f17])).
% 1.45/0.57  fof(f17,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f7])).
% 1.45/0.57  fof(f7,axiom,(
% 1.45/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_subset_1)).
% 1.45/0.57  fof(f44,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f19])).
% 1.45/0.57  fof(f19,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 1.45/0.57    inference(flattening,[],[f18])).
% 1.45/0.57  fof(f18,plain,(
% 1.45/0.57    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f12])).
% 1.45/0.57  fof(f12,axiom,(
% 1.45/0.57    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 1.45/0.57  fof(f128,plain,(
% 1.45/0.57    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_7),
% 1.45/0.57    inference(avatar_component_clause,[],[f126])).
% 1.45/0.57  fof(f94,plain,(
% 1.45/0.57    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl3_5),
% 1.45/0.57    inference(avatar_component_clause,[],[f92])).
% 1.45/0.57  fof(f79,plain,(
% 1.45/0.57    v1_zfmisc_1(sK0) | ~spl3_2),
% 1.45/0.57    inference(avatar_component_clause,[],[f77])).
% 1.45/0.57  fof(f140,plain,(
% 1.45/0.57    spl3_8 | spl3_1 | ~spl3_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f115,f82,f72,f137])).
% 1.45/0.57  fof(f72,plain,(
% 1.45/0.57    spl3_1 <=> v1_xboole_0(sK0)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.45/0.57  fof(f82,plain,(
% 1.45/0.57    spl3_3 <=> m1_subset_1(sK1,sK0)),
% 1.45/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.45/0.57  fof(f115,plain,(
% 1.45/0.57    k6_domain_1(sK0,sK1) = k1_enumset1(sK1,sK1,sK1) | (spl3_1 | ~spl3_3)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f74,f84,f58])).
% 1.45/0.57  fof(f58,plain,(
% 1.45/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | v1_xboole_0(X0)) )),
% 1.45/0.57    inference(definition_unfolding,[],[f46,f57])).
% 1.45/0.57  fof(f57,plain,(
% 1.45/0.57    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.45/0.57    inference(definition_unfolding,[],[f42,f45])).
% 1.45/0.57  fof(f42,plain,(
% 1.45/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f4])).
% 1.45/0.57  fof(f4,axiom,(
% 1.45/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.57  fof(f46,plain,(
% 1.45/0.57    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f21])).
% 1.45/0.57  fof(f21,plain,(
% 1.45/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.45/0.57    inference(flattening,[],[f20])).
% 1.45/0.57  fof(f20,plain,(
% 1.45/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f11])).
% 1.45/0.57  fof(f11,axiom,(
% 1.45/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.45/0.57  fof(f84,plain,(
% 1.45/0.57    m1_subset_1(sK1,sK0) | ~spl3_3),
% 1.45/0.57    inference(avatar_component_clause,[],[f82])).
% 1.45/0.57  fof(f74,plain,(
% 1.45/0.57    ~v1_xboole_0(sK0) | spl3_1),
% 1.45/0.57    inference(avatar_component_clause,[],[f72])).
% 1.45/0.57  fof(f129,plain,(
% 1.45/0.57    spl3_7 | spl3_1 | ~spl3_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f110,f82,f72,f126])).
% 1.45/0.57  fof(f110,plain,(
% 1.45/0.57    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (spl3_1 | ~spl3_3)),
% 1.45/0.57    inference(unit_resulting_resolution,[],[f74,f84,f47])).
% 1.45/0.57  fof(f47,plain,(
% 1.45/0.57    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.45/0.57    inference(cnf_transformation,[],[f23])).
% 1.45/0.57  fof(f23,plain,(
% 1.45/0.57    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.45/0.57    inference(flattening,[],[f22])).
% 1.45/0.57  fof(f22,plain,(
% 1.45/0.57    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.45/0.57    inference(ennf_transformation,[],[f10])).
% 1.45/0.57  fof(f10,axiom,(
% 1.45/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.45/0.57  fof(f95,plain,(
% 1.45/0.57    spl3_5),
% 1.45/0.57    inference(avatar_split_clause,[],[f38,f92])).
% 1.45/0.57  fof(f38,plain,(
% 1.45/0.57    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.45/0.57    inference(cnf_transformation,[],[f30])).
% 1.45/0.57  fof(f30,plain,(
% 1.45/0.57    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 1.45/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f29,f28])).
% 1.45/0.57  % (30496)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.45/0.57  fof(f28,plain,(
% 1.45/0.57    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  fof(f29,plain,(
% 1.45/0.57    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 1.45/0.57    introduced(choice_axiom,[])).
% 1.45/0.57  % (30493)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.45/0.57  fof(f16,plain,(
% 1.45/0.57    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.45/0.57    inference(flattening,[],[f15])).
% 1.45/0.57  fof(f15,plain,(
% 1.45/0.57    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.45/0.57    inference(ennf_transformation,[],[f14])).
% 1.45/0.57  fof(f14,negated_conjecture,(
% 1.45/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.45/0.57    inference(negated_conjecture,[],[f13])).
% 1.45/0.57  fof(f13,conjecture,(
% 1.45/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 1.45/0.57  fof(f90,plain,(
% 1.45/0.57    spl3_4),
% 1.45/0.57    inference(avatar_split_clause,[],[f40,f87])).
% 1.45/0.57  fof(f40,plain,(
% 1.45/0.57    v1_xboole_0(k1_xboole_0)),
% 1.45/0.57    inference(cnf_transformation,[],[f1])).
% 1.45/0.57  fof(f1,axiom,(
% 1.45/0.57    v1_xboole_0(k1_xboole_0)),
% 1.45/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.45/0.57  fof(f85,plain,(
% 1.45/0.57    spl3_3),
% 1.45/0.57    inference(avatar_split_clause,[],[f37,f82])).
% 1.45/0.57  fof(f37,plain,(
% 1.45/0.57    m1_subset_1(sK1,sK0)),
% 1.45/0.57    inference(cnf_transformation,[],[f30])).
% 1.45/0.57  fof(f80,plain,(
% 1.45/0.57    spl3_2),
% 1.45/0.57    inference(avatar_split_clause,[],[f39,f77])).
% 1.45/0.57  fof(f39,plain,(
% 1.45/0.57    v1_zfmisc_1(sK0)),
% 1.45/0.57    inference(cnf_transformation,[],[f30])).
% 1.45/0.57  fof(f75,plain,(
% 1.45/0.57    ~spl3_1),
% 1.45/0.57    inference(avatar_split_clause,[],[f36,f72])).
% 1.45/0.57  fof(f36,plain,(
% 1.45/0.57    ~v1_xboole_0(sK0)),
% 1.45/0.57    inference(cnf_transformation,[],[f30])).
% 1.45/0.57  % SZS output end Proof for theBenchmark
% 1.45/0.57  % (30511)------------------------------
% 1.45/0.57  % (30511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (30511)Termination reason: Refutation
% 1.45/0.57  
% 1.45/0.57  % (30511)Memory used [KB]: 10746
% 1.45/0.57  % (30511)Time elapsed: 0.139 s
% 1.45/0.57  % (30511)------------------------------
% 1.45/0.57  % (30511)------------------------------
% 1.45/0.57  % (30497)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.58  % (30490)Success in time 0.211 s
%------------------------------------------------------------------------------
