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
% DateTime   : Thu Dec  3 13:20:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 137 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :    7
%              Number of atoms          :  233 ( 423 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f60,f64,f73,f77,f84,f93,f102,f109,f113,f121])).

fof(f121,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f116,f118])).

fof(f118,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_tarski(X0))
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(superposition,[],[f112,f59])).

fof(f59,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_6
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f112,plain,
    ( ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl2_15
  <=> ! [X1,X0] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f116,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f36,f41,f101,f108,f92])).

fof(f92,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f108,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl2_14
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f101,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_13
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f41,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f36,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f113,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f69,f62,f54,f111])).

fof(f54,plain,
    ( spl2_5
  <=> ! [X1,X0,X2] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f62,plain,
    ( spl2_7
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f69,plain,
    ( ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(superposition,[],[f55,f63])).

fof(f63,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f55,plain,
    ( ! [X2,X0,X1] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f109,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_14
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f79,f71,f49,f106,f44,f34])).

fof(f44,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f49,plain,
    ( spl2_4
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f71,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f79,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(superposition,[],[f51,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f51,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f102,plain,
    ( spl2_13
    | spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f89,f81,f75,f44,f34,f99])).

fof(f75,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f81,plain,
    ( spl2_11
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f89,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_10
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f85,f83])).

fof(f83,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f85,plain,
    ( m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f36,f46,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f46,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f93,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f28,f91])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f84,plain,
    ( spl2_11
    | spl2_1
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f78,f71,f44,f34,f81])).

fof(f78,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | spl2_1
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f36,f46,f72])).

fof(f77,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f73,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f64,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    ! [X2,X0,X1] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : ~ v1_xboole_0(k1_enumset1(X0,X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_subset_1)).

fof(f52,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).

fof(f19,plain,
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

fof(f20,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f47,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f39])).

fof(f25,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f22,f34])).

fof(f22,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (19095)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.43  % (19095)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f37,f42,f47,f52,f56,f60,f64,f73,f77,f84,f93,f102,f109,f113,f121])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    $false | (spl2_1 | ~spl2_2 | ~spl2_6 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_15)),
% 0.20/0.43    inference(subsumption_resolution,[],[f116,f118])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) ) | (~spl2_6 | ~spl2_15)),
% 0.20/0.43    inference(superposition,[],[f112,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl2_6 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) ) | ~spl2_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f111])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    spl2_15 <=> ! [X1,X0] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    v1_xboole_0(k1_tarski(sK1)) | (spl2_1 | ~spl2_2 | ~spl2_12 | ~spl2_13 | ~spl2_14)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f36,f41,f101,f108,f92])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f91])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    spl2_12 <=> ! [X1,X0] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f106])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    spl2_14 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f99])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    spl2_13 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    v1_zfmisc_1(sK0) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    spl2_2 <=> v1_zfmisc_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ~v1_xboole_0(sK0) | spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    spl2_1 <=> v1_xboole_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    spl2_15 | ~spl2_5 | ~spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f69,f62,f54,f111])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    spl2_5 <=> ! [X1,X0,X2] : ~v1_xboole_0(k1_enumset1(X0,X1,X2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    spl2_7 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) ) | (~spl2_5 | ~spl2_7)),
% 0.20/0.43    inference(superposition,[],[f55,f63])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f62])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_xboole_0(k1_enumset1(X0,X1,X2))) ) | ~spl2_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f54])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    spl2_1 | ~spl2_3 | spl2_14 | ~spl2_4 | ~spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f79,f71,f49,f106,f44,f34])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl2_4 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl2_9 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    v1_subset_1(k1_tarski(sK1),sK0) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_4 | ~spl2_9)),
% 0.20/0.43    inference(superposition,[],[f51,f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f49])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    spl2_13 | spl2_1 | ~spl2_3 | ~spl2_10 | ~spl2_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f89,f81,f75,f44,f34,f99])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    spl2_10 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl2_11 <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_10 | ~spl2_11)),
% 0.20/0.43    inference(forward_demodulation,[],[f85,f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | ~spl2_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_3 | ~spl2_10)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f36,f46,f76])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f75])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f44])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    spl2_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f91])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl2_11 | spl2_1 | ~spl2_3 | ~spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f78,f71,f44,f34,f81])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | (spl2_1 | ~spl2_3 | ~spl2_9)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f36,f46,f72])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl2_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f75])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl2_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f30,f71])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f62])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f26,f58])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    spl2_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f54])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v1_xboole_0(k1_enumset1(X0,X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ~v1_xboole_0(k1_enumset1(X0,X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_subset_1)).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f49])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.43    inference(negated_conjecture,[],[f8])).
% 0.20/0.43  fof(f8,conjecture,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f44])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    m1_subset_1(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f39])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    v1_zfmisc_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f34])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ~v1_xboole_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (19095)------------------------------
% 0.20/0.43  % (19095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (19095)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (19095)Memory used [KB]: 6140
% 0.20/0.43  % (19095)Time elapsed: 0.046 s
% 0.20/0.43  % (19095)------------------------------
% 0.20/0.43  % (19095)------------------------------
% 0.20/0.43  % (19089)Success in time 0.079 s
%------------------------------------------------------------------------------
