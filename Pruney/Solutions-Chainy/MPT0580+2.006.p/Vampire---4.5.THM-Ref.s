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
% DateTime   : Thu Dec  3 12:50:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 504 expanded)
%              Number of leaves         :   16 ( 160 expanded)
%              Depth                    :   18
%              Number of atoms          :  189 ( 952 expanded)
%              Number of equality atoms :   26 ( 303 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f473,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f81,f97,f358,f472])).

fof(f472,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f434,f80,f363,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f363,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f361,f51])).

fof(f51,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f30,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f361,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f25,f64,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v3_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

fof(f64,plain,
    ( v3_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_1
  <=> v3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

fof(f80,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_3
  <=> r2_hidden(sK1,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f434,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f375,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f375,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f374,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f374,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f29,f69,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f69,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f358,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f134,f58,f321,f34])).

fof(f321,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f249,f309])).

fof(f309,plain,
    ( k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f135,f249,f106])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k2_relat_1(sK0))
        | ~ r2_hidden(X0,X1)
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(resolution,[],[f96,f34])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_xboole_0 = X1 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_4
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f135,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k2_relat_1(sK0))
    | spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f132,f51])).

fof(f132,plain,
    ( r1_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_relat_1(sK0))
    | spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f127,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f74,f96])).

fof(f74,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),k2_relat_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f72,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | spl3_1 ),
    inference(forward_demodulation,[],[f71,f51])).

fof(f71,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f25,f65,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | v3_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | v3_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,
    ( ~ v3_relat_1(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f127,plain,
    ( r1_tarski(k2_enumset1(sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),k2_relat_1(sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f74,f74,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f249,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f247,f35])).

fof(f247,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f166,f51])).

fof(f166,plain,
    ( ! [X0] : ~ r1_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f156,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f156,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f29,f134,f34])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f134,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl3_1
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f75,f121])).

fof(f75,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f72,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,
    ( spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f24,f95,f63])).

fof(f24,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK0))
      | k1_xboole_0 = X1
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f22,f78,f63])).

fof(f22,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f67,f63])).

fof(f23,plain,
    ( k1_xboole_0 != sK1
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:12:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (26740)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (26748)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (26740)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (26756)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (26764)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f473,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f70,f81,f97,f358,f472])).
% 0.22/0.53  fof(f472,plain,(
% 0.22/0.53    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f467])).
% 0.22/0.53  fof(f467,plain,(
% 0.22/0.53    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f434,f80,f363,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f363,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~spl3_1),
% 0.22/0.53    inference(forward_demodulation,[],[f361,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.53    inference(definition_unfolding,[],[f30,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f40,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f44,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.53  fof(f361,plain,(
% 0.22/0.53    r1_tarski(k2_relat_1(sK0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f25,f64,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_relat_1(X0) | r1_tarski(k2_relat_1(X0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f39,f50])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    v3_relat_1(sK0) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl3_1 <=> v3_relat_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f16])).
% 0.22/0.53  fof(f16,conjecture,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    r2_hidden(sK1,k2_relat_1(sK0)) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl3_3 <=> r2_hidden(sK1,k2_relat_1(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f434,plain,(
% 0.22/0.53    ~r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) | spl3_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f375,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.53  fof(f375,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | spl3_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f374,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f374,plain,(
% 0.22/0.53    ~r1_tarski(sK1,k1_xboole_0) | spl3_2),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f29,f69,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl3_2 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    spl3_1 | ~spl3_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f345])).
% 0.22/0.53  fof(f345,plain,(
% 0.22/0.53    $false | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f134,f58,f321,f34])).
% 0.22/0.53  fof(f321,plain,(
% 0.22/0.53    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(backward_demodulation,[],[f249,f309])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    k1_xboole_0 = sK2(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f135,f249,f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,k2_relat_1(sK0)) | ~r2_hidden(X0,X1) | k1_xboole_0 = X0) ) | ~spl3_4),
% 0.22/0.53    inference(resolution,[],[f96,f34])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1) ) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl3_4 <=> ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    r1_tarski(k1_zfmisc_1(k1_xboole_0),k2_relat_1(sK0)) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(forward_demodulation,[],[f132,f51])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    r1_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_relat_1(sK0)) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(backward_demodulation,[],[f127,f121])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f74,f96])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    r2_hidden(sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),k2_relat_1(sK0)) | spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f72,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | spl3_1),
% 0.22/0.53    inference(forward_demodulation,[],[f71,f51])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f25,f65,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | v3_relat_1(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f38,f50])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | v3_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ~v3_relat_1(sK0) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    r1_tarski(k2_enumset1(sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),k2_relat_1(sK0)) | spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f74,f74,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f33,f48])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    r2_hidden(sK2(k1_zfmisc_1(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f247,f35])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    ~r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(superposition,[],[f166,f51])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0),k1_xboole_0)) ) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f156,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f31,f48])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ~r2_hidden(k1_xboole_0,k1_xboole_0) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f29,f134,f34])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl3_1 | ~spl3_4)),
% 0.22/0.53    inference(backward_demodulation,[],[f75,f121])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ~r2_hidden(sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | spl3_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f72,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl3_1 | spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f24,f95,f63])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_xboole_0 = X1 | v3_relat_1(sK0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ~spl3_1 | spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f22,f78,f63])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    r2_hidden(sK1,k2_relat_1(sK0)) | ~v3_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f23,f67,f63])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | ~v3_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (26740)------------------------------
% 0.22/0.53  % (26740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (26740)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (26740)Memory used [KB]: 6396
% 0.22/0.53  % (26740)Time elapsed: 0.112 s
% 0.22/0.53  % (26740)------------------------------
% 0.22/0.53  % (26740)------------------------------
% 0.22/0.53  % (26735)Success in time 0.168 s
%------------------------------------------------------------------------------
