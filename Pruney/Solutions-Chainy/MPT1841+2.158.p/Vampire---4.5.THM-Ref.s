%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:30 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 132 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 ( 397 expanded)
%              Number of equality atoms :   47 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f69,f80,f83,f126])).

fof(f126,plain,(
    ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | ~ spl2_4 ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_4 ),
    inference(superposition,[],[f122,f47])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f122,plain,
    ( ! [X0] : k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))
    | ~ spl2_4 ),
    inference(superposition,[],[f48,f121])).

fof(f121,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f120,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_4
  <=> k1_xboole_0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f120,plain,(
    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f117,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k2_tarski(X0,X0) = k6_domain_1(sK0,X0) ) ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f48,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f39,f46,f35])).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

% (30482)Termination reason: Refutation not found, incomplete strategy
fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f83,plain,(
    ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f82])).

% (30482)Memory used [KB]: 10874
fof(f82,plain,
    ( $false
    | ~ spl2_5 ),
    inference(resolution,[],[f81,f50])).

% (30482)Time elapsed: 0.081 s
% (30482)------------------------------
% (30482)------------------------------
fof(f50,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f33,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f81,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl2_5 ),
    inference(backward_demodulation,[],[f31,f79])).

fof(f79,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_5
  <=> sK0 = k6_domain_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f31,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f80,plain,
    ( spl2_4
    | spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f71,f64,f77,f73])).

fof(f64,plain,
    ( spl2_3
  <=> ! [X0] :
        ( v1_xboole_0(k6_domain_1(sK0,X0))
        | ~ m1_subset_1(X0,sK0)
        | sK0 = k6_domain_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f71,plain,
    ( sK0 = k6_domain_1(sK0,sK1)
    | k1_xboole_0 = k6_domain_1(sK0,sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f70,f30])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | sK0 = k6_domain_1(sK0,X0)
        | k1_xboole_0 = k6_domain_1(sK0,X0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f65,f37])).

% (30490)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f65,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_domain_1(sK0,X0))
        | ~ m1_subset_1(X0,sK0)
        | sK0 = k6_domain_1(sK0,X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f69,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_1 ),
    inference(resolution,[],[f57,f29])).

fof(f57,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f66,plain,
    ( spl2_1
    | spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f62,f59,f64,f55])).

fof(f59,plain,
    ( spl2_2
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f62,plain,
    ( ! [X0] :
        ( v1_xboole_0(k6_domain_1(sK0,X0))
        | sK0 = k6_domain_1(sK0,X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f60,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_domain_1(X1,X0),X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f60,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f53,f59,f55])).

fof(f53,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | v1_xboole_0(sK0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f36,f32])).

fof(f32,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : run_vampire %s %d
% 0.06/0.26  % Computer   : n018.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 17:02:56 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.11/0.39  % (30474)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.39  % (30482)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.11/0.40  % (30482)Refutation not found, incomplete strategy% (30482)------------------------------
% 0.11/0.40  % (30482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (30474)Refutation found. Thanks to Tanya!
% 0.11/0.40  % SZS status Theorem for theBenchmark
% 0.11/0.40  % SZS output start Proof for theBenchmark
% 0.11/0.40  fof(f127,plain,(
% 0.11/0.40    $false),
% 0.11/0.40    inference(avatar_sat_refutation,[],[f61,f66,f69,f80,f83,f126])).
% 0.11/0.40  fof(f126,plain,(
% 0.11/0.40    ~spl2_4),
% 0.11/0.40    inference(avatar_contradiction_clause,[],[f125])).
% 0.11/0.40  fof(f125,plain,(
% 0.11/0.40    $false | ~spl2_4),
% 0.11/0.40    inference(trivial_inequality_removal,[],[f124])).
% 0.11/0.40  fof(f124,plain,(
% 0.11/0.40    k1_xboole_0 != k1_xboole_0 | ~spl2_4),
% 0.11/0.40    inference(superposition,[],[f122,f47])).
% 0.11/0.40  fof(f47,plain,(
% 0.11/0.40    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 0.11/0.40    inference(definition_unfolding,[],[f38,f46])).
% 0.11/0.40  fof(f46,plain,(
% 0.11/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.11/0.40    inference(definition_unfolding,[],[f41,f40])).
% 0.11/0.40  fof(f40,plain,(
% 0.11/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.11/0.40    inference(cnf_transformation,[],[f3])).
% 0.11/0.40  fof(f3,axiom,(
% 0.11/0.40    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.11/0.40  fof(f41,plain,(
% 0.11/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.11/0.40    inference(cnf_transformation,[],[f4])).
% 0.11/0.40  fof(f4,axiom,(
% 0.11/0.40    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.11/0.40  fof(f38,plain,(
% 0.11/0.40    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.11/0.40    inference(cnf_transformation,[],[f15])).
% 0.11/0.40  fof(f15,plain,(
% 0.11/0.40    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.11/0.40    inference(rectify,[],[f1])).
% 0.11/0.40  fof(f1,axiom,(
% 0.11/0.40    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.11/0.40  fof(f122,plain,(
% 0.11/0.40    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) ) | ~spl2_4),
% 0.11/0.40    inference(superposition,[],[f48,f121])).
% 0.11/0.40  fof(f121,plain,(
% 0.11/0.40    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl2_4),
% 0.11/0.40    inference(forward_demodulation,[],[f120,f75])).
% 0.11/0.40  fof(f75,plain,(
% 0.11/0.40    k1_xboole_0 = k6_domain_1(sK0,sK1) | ~spl2_4),
% 0.11/0.40    inference(avatar_component_clause,[],[f73])).
% 0.11/0.40  fof(f73,plain,(
% 0.11/0.40    spl2_4 <=> k1_xboole_0 = k6_domain_1(sK0,sK1)),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.11/0.40  fof(f120,plain,(
% 0.11/0.40    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)),
% 0.11/0.40    inference(resolution,[],[f117,f30])).
% 0.11/0.40  fof(f30,plain,(
% 0.11/0.40    m1_subset_1(sK1,sK0)),
% 0.11/0.40    inference(cnf_transformation,[],[f27])).
% 0.11/0.40  fof(f27,plain,(
% 0.11/0.40    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.11/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f26,f25])).
% 0.11/0.40  fof(f25,plain,(
% 0.11/0.40    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f26,plain,(
% 0.11/0.40    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.11/0.40    introduced(choice_axiom,[])).
% 0.11/0.40  fof(f17,plain,(
% 0.11/0.40    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.11/0.40    inference(flattening,[],[f16])).
% 0.11/0.40  fof(f16,plain,(
% 0.11/0.40    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.11/0.40    inference(ennf_transformation,[],[f14])).
% 0.11/0.40  fof(f14,negated_conjecture,(
% 0.11/0.40    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.11/0.40    inference(negated_conjecture,[],[f13])).
% 0.11/0.40  fof(f13,conjecture,(
% 0.11/0.40    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.11/0.40  fof(f117,plain,(
% 0.11/0.40    ( ! [X0] : (~m1_subset_1(X0,sK0) | k2_tarski(X0,X0) = k6_domain_1(sK0,X0)) )),
% 0.11/0.40    inference(resolution,[],[f49,f29])).
% 0.11/0.40  fof(f29,plain,(
% 0.11/0.40    ~v1_xboole_0(sK0)),
% 0.11/0.40    inference(cnf_transformation,[],[f27])).
% 0.11/0.40  fof(f49,plain,(
% 0.11/0.40    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.11/0.40    inference(definition_unfolding,[],[f42,f35])).
% 0.11/0.40  fof(f35,plain,(
% 0.11/0.40    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f5])).
% 0.11/0.40  fof(f5,axiom,(
% 0.11/0.40    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.11/0.40  fof(f42,plain,(
% 0.11/0.40    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f22])).
% 0.11/0.40  fof(f22,plain,(
% 0.11/0.40    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.11/0.40    inference(flattening,[],[f21])).
% 0.11/0.40  fof(f21,plain,(
% 0.11/0.40    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.11/0.40    inference(ennf_transformation,[],[f11])).
% 0.11/0.40  fof(f11,axiom,(
% 0.11/0.40    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.11/0.40  fof(f48,plain,(
% 0.11/0.40    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,k2_tarski(X0,X0))))) )),
% 0.11/0.40    inference(definition_unfolding,[],[f39,f46,f35])).
% 0.11/0.40  fof(f39,plain,(
% 0.11/0.40    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f6])).
% 0.11/0.40  % (30482)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.40  fof(f6,axiom,(
% 0.11/0.40    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.11/0.40  
% 0.11/0.40  fof(f83,plain,(
% 0.11/0.40    ~spl2_5),
% 0.11/0.40    inference(avatar_contradiction_clause,[],[f82])).
% 0.11/0.40  % (30482)Memory used [KB]: 10874
% 0.11/0.40  fof(f82,plain,(
% 0.11/0.40    $false | ~spl2_5),
% 0.11/0.40    inference(resolution,[],[f81,f50])).
% 0.11/0.40  % (30482)Time elapsed: 0.081 s
% 0.11/0.40  % (30482)------------------------------
% 0.11/0.40  % (30482)------------------------------
% 0.11/0.40  fof(f50,plain,(
% 0.11/0.40    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.11/0.40    inference(backward_demodulation,[],[f33,f34])).
% 0.11/0.40  fof(f34,plain,(
% 0.11/0.40    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.11/0.40    inference(cnf_transformation,[],[f7])).
% 0.11/0.40  fof(f7,axiom,(
% 0.11/0.40    ! [X0] : k2_subset_1(X0) = X0),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.11/0.40  fof(f33,plain,(
% 0.11/0.40    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f8])).
% 0.11/0.40  fof(f8,axiom,(
% 0.11/0.40    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 0.11/0.40  fof(f81,plain,(
% 0.11/0.40    v1_subset_1(sK0,sK0) | ~spl2_5),
% 0.11/0.40    inference(backward_demodulation,[],[f31,f79])).
% 0.11/0.40  fof(f79,plain,(
% 0.11/0.40    sK0 = k6_domain_1(sK0,sK1) | ~spl2_5),
% 0.11/0.40    inference(avatar_component_clause,[],[f77])).
% 0.11/0.40  fof(f77,plain,(
% 0.11/0.40    spl2_5 <=> sK0 = k6_domain_1(sK0,sK1)),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.11/0.40  fof(f31,plain,(
% 0.11/0.40    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.11/0.40    inference(cnf_transformation,[],[f27])).
% 0.11/0.40  fof(f80,plain,(
% 0.11/0.40    spl2_4 | spl2_5 | ~spl2_3),
% 0.11/0.40    inference(avatar_split_clause,[],[f71,f64,f77,f73])).
% 0.11/0.40  fof(f64,plain,(
% 0.11/0.40    spl2_3 <=> ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | ~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0))),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.11/0.40  fof(f71,plain,(
% 0.11/0.40    sK0 = k6_domain_1(sK0,sK1) | k1_xboole_0 = k6_domain_1(sK0,sK1) | ~spl2_3),
% 0.11/0.40    inference(resolution,[],[f70,f30])).
% 0.11/0.40  fof(f70,plain,(
% 0.11/0.40    ( ! [X0] : (~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0) | k1_xboole_0 = k6_domain_1(sK0,X0)) ) | ~spl2_3),
% 0.11/0.40    inference(resolution,[],[f65,f37])).
% 0.11/0.40  % (30490)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.11/0.40  fof(f37,plain,(
% 0.11/0.40    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.11/0.40    inference(cnf_transformation,[],[f20])).
% 0.11/0.40  fof(f20,plain,(
% 0.11/0.40    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.11/0.40    inference(ennf_transformation,[],[f2])).
% 0.11/0.40  fof(f2,axiom,(
% 0.11/0.40    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.11/0.40  fof(f65,plain,(
% 0.11/0.40    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | ~m1_subset_1(X0,sK0) | sK0 = k6_domain_1(sK0,X0)) ) | ~spl2_3),
% 0.11/0.40    inference(avatar_component_clause,[],[f64])).
% 0.11/0.40  fof(f69,plain,(
% 0.11/0.40    ~spl2_1),
% 0.11/0.40    inference(avatar_contradiction_clause,[],[f67])).
% 0.11/0.40  fof(f67,plain,(
% 0.11/0.40    $false | ~spl2_1),
% 0.11/0.40    inference(resolution,[],[f57,f29])).
% 0.11/0.40  fof(f57,plain,(
% 0.11/0.40    v1_xboole_0(sK0) | ~spl2_1),
% 0.11/0.40    inference(avatar_component_clause,[],[f55])).
% 0.11/0.40  fof(f55,plain,(
% 0.11/0.40    spl2_1 <=> v1_xboole_0(sK0)),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.11/0.40  fof(f66,plain,(
% 0.11/0.40    spl2_1 | spl2_3 | ~spl2_2),
% 0.11/0.40    inference(avatar_split_clause,[],[f62,f59,f64,f55])).
% 0.11/0.40  fof(f59,plain,(
% 0.11/0.40    spl2_2 <=> ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0)),
% 0.11/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.11/0.40  fof(f62,plain,(
% 0.11/0.40    ( ! [X0] : (v1_xboole_0(k6_domain_1(sK0,X0)) | sK0 = k6_domain_1(sK0,X0) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0)) ) | ~spl2_2),
% 0.11/0.40    inference(resolution,[],[f60,f51])).
% 0.11/0.40  fof(f51,plain,(
% 0.11/0.40    ( ! [X0,X1] : (r1_tarski(k6_domain_1(X1,X0),X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.11/0.40    inference(resolution,[],[f43,f44])).
% 0.11/0.40  fof(f44,plain,(
% 0.11/0.40    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f28])).
% 0.11/0.40  fof(f28,plain,(
% 0.11/0.40    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.11/0.40    inference(nnf_transformation,[],[f9])).
% 0.11/0.40  fof(f9,axiom,(
% 0.11/0.40    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.11/0.40  fof(f43,plain,(
% 0.11/0.40    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f24])).
% 0.11/0.40  fof(f24,plain,(
% 0.11/0.40    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.11/0.40    inference(flattening,[],[f23])).
% 0.11/0.40  fof(f23,plain,(
% 0.11/0.40    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.11/0.40    inference(ennf_transformation,[],[f10])).
% 0.11/0.40  fof(f10,axiom,(
% 0.11/0.40    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.11/0.40  fof(f60,plain,(
% 0.11/0.40    ( ! [X0] : (~r1_tarski(X0,sK0) | v1_xboole_0(X0) | sK0 = X0) ) | ~spl2_2),
% 0.11/0.40    inference(avatar_component_clause,[],[f59])).
% 0.11/0.40  fof(f61,plain,(
% 0.11/0.40    spl2_1 | spl2_2),
% 0.11/0.40    inference(avatar_split_clause,[],[f53,f59,f55])).
% 0.11/0.40  fof(f53,plain,(
% 0.11/0.40    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | v1_xboole_0(sK0) | v1_xboole_0(X0)) )),
% 0.11/0.40    inference(resolution,[],[f36,f32])).
% 0.11/0.40  fof(f32,plain,(
% 0.11/0.40    v1_zfmisc_1(sK0)),
% 0.11/0.40    inference(cnf_transformation,[],[f27])).
% 0.11/0.40  fof(f36,plain,(
% 0.11/0.40    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.11/0.40    inference(cnf_transformation,[],[f19])).
% 0.11/0.40  fof(f19,plain,(
% 0.11/0.40    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.11/0.40    inference(flattening,[],[f18])).
% 0.11/0.40  fof(f18,plain,(
% 0.11/0.40    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.11/0.40    inference(ennf_transformation,[],[f12])).
% 0.11/0.40  fof(f12,axiom,(
% 0.11/0.40    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.11/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.11/0.40  % SZS output end Proof for theBenchmark
% 0.11/0.40  % (30474)------------------------------
% 0.11/0.40  % (30474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.40  % (30474)Termination reason: Refutation
% 0.11/0.40  
% 0.11/0.40  % (30474)Memory used [KB]: 6268
% 0.11/0.40  % (30474)Time elapsed: 0.080 s
% 0.11/0.40  % (30474)------------------------------
% 0.11/0.40  % (30474)------------------------------
% 0.11/0.40  % (30484)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.11/0.40  % (30457)Success in time 0.125 s
%------------------------------------------------------------------------------
