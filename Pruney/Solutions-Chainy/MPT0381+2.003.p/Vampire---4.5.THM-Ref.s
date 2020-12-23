%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:35 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 133 expanded)
%              Number of leaves         :   21 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :  175 ( 261 expanded)
%              Number of equality atoms :   30 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f87,f121,f124,f155,f190,f204,f239,f241])).

fof(f241,plain,
    ( ~ spl4_5
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_15 ),
    inference(resolution,[],[f213,f117])).

fof(f117,plain,
    ( v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl4_5
  <=> v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f213,plain,
    ( ! [X7] : ~ v1_xboole_0(X7)
    | ~ spl4_15 ),
    inference(resolution,[],[f199,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f199,plain,
    ( ! [X0] : r2_hidden(sK0,X0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl4_15
  <=> ! [X0] : r2_hidden(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f239,plain,
    ( ~ spl4_5
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f230,f201,f115])).

fof(f201,plain,
    ( spl4_16
  <=> r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f230,plain,
    ( ~ v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl4_16 ),
    inference(resolution,[],[f203,f27])).

fof(f203,plain,
    ( r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f204,plain,
    ( spl4_15
    | spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f196,f187,f201,f198])).

fof(f187,plain,
    ( spl4_14
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f196,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | r2_hidden(sK0,X0) )
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f191,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f191,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )
    | ~ spl4_14 ),
    inference(resolution,[],[f189,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f189,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f187])).

fof(f190,plain,
    ( spl4_14
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f170,f152,f69,f187])).

fof(f69,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f152,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f170,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(backward_demodulation,[],[f71,f154])).

fof(f154,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f71,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f155,plain,
    ( spl4_1
    | spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f148,f84,f152,f64])).

fof(f64,plain,
    ( spl4_1
  <=> m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f84,plain,
    ( spl4_4
  <=> m1_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f148,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f53,f86])).

fof(f86,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0
      | m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_xboole_0 = X0
      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f124,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f123,f119,f115])).

fof(f119,plain,
    ( spl4_6
  <=> ! [X0] : ~ r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f123,plain,
    ( v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl4_6 ),
    inference(resolution,[],[f120,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f120,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f121,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f113,f119,f115])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0)
      | v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0)) ) ),
    inference(resolution,[],[f106,f26])).

fof(f106,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X9,X8) ) ),
    inference(superposition,[],[f61,f93])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f30])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f81,f69,f84])).

fof(f81,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f73,f71])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f72,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f69])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f67,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f52,f64])).

fof(f52,plain,(
    ~ m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) ),
    inference(definition_unfolding,[],[f23,f51])).

fof(f23,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:13:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.35/0.55  % (10014)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.56  % (10039)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.56  % (10019)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.35/0.56  % (10025)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.56  % (10037)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.35/0.56  % (10040)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.56  % (10044)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.57  % (10026)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.57  % (10030)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.57  % (10036)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.35/0.57  % (10015)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.57  % (10035)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.57  % (10015)Refutation not found, incomplete strategy% (10015)------------------------------
% 1.35/0.57  % (10015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (10015)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (10015)Memory used [KB]: 10746
% 1.35/0.57  % (10015)Time elapsed: 0.150 s
% 1.35/0.57  % (10015)------------------------------
% 1.35/0.57  % (10015)------------------------------
% 1.35/0.57  % (10022)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.57  % (10022)Refutation not found, incomplete strategy% (10022)------------------------------
% 1.35/0.57  % (10022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (10022)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (10022)Memory used [KB]: 10746
% 1.35/0.57  % (10022)Time elapsed: 0.158 s
% 1.35/0.57  % (10022)------------------------------
% 1.35/0.57  % (10022)------------------------------
% 1.35/0.57  % (10025)Refutation not found, incomplete strategy% (10025)------------------------------
% 1.35/0.57  % (10025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.57  % (10031)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.57  % (10025)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.57  
% 1.35/0.57  % (10025)Memory used [KB]: 10618
% 1.35/0.57  % (10025)Time elapsed: 0.135 s
% 1.35/0.57  % (10025)------------------------------
% 1.35/0.57  % (10025)------------------------------
% 1.35/0.58  % (10031)Refutation found. Thanks to Tanya!
% 1.35/0.58  % SZS status Theorem for theBenchmark
% 1.35/0.58  % SZS output start Proof for theBenchmark
% 1.35/0.58  fof(f242,plain,(
% 1.35/0.58    $false),
% 1.35/0.58    inference(avatar_sat_refutation,[],[f67,f72,f87,f121,f124,f155,f190,f204,f239,f241])).
% 1.35/0.58  fof(f241,plain,(
% 1.35/0.58    ~spl4_5 | ~spl4_15),
% 1.35/0.58    inference(avatar_contradiction_clause,[],[f240])).
% 1.35/0.58  fof(f240,plain,(
% 1.35/0.58    $false | (~spl4_5 | ~spl4_15)),
% 1.35/0.58    inference(resolution,[],[f213,f117])).
% 1.35/0.58  fof(f117,plain,(
% 1.35/0.58    v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl4_5),
% 1.35/0.58    inference(avatar_component_clause,[],[f115])).
% 1.35/0.58  fof(f115,plain,(
% 1.35/0.58    spl4_5 <=> v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.35/0.58  fof(f213,plain,(
% 1.35/0.58    ( ! [X7] : (~v1_xboole_0(X7)) ) | ~spl4_15),
% 1.35/0.58    inference(resolution,[],[f199,f27])).
% 1.35/0.58  fof(f27,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f2])).
% 1.35/0.58  fof(f2,axiom,(
% 1.35/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.35/0.58  fof(f199,plain,(
% 1.35/0.58    ( ! [X0] : (r2_hidden(sK0,X0)) ) | ~spl4_15),
% 1.35/0.58    inference(avatar_component_clause,[],[f198])).
% 1.35/0.58  fof(f198,plain,(
% 1.35/0.58    spl4_15 <=> ! [X0] : r2_hidden(sK0,X0)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.35/0.58  fof(f239,plain,(
% 1.35/0.58    ~spl4_5 | ~spl4_16),
% 1.35/0.58    inference(avatar_split_clause,[],[f230,f201,f115])).
% 1.35/0.58  fof(f201,plain,(
% 1.35/0.58    spl4_16 <=> r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.35/0.58  fof(f230,plain,(
% 1.35/0.58    ~v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl4_16),
% 1.35/0.58    inference(resolution,[],[f203,f27])).
% 1.35/0.58  fof(f203,plain,(
% 1.35/0.58    r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl4_16),
% 1.35/0.58    inference(avatar_component_clause,[],[f201])).
% 1.35/0.58  fof(f204,plain,(
% 1.35/0.58    spl4_15 | spl4_16 | ~spl4_14),
% 1.35/0.58    inference(avatar_split_clause,[],[f196,f187,f201,f198])).
% 1.35/0.58  fof(f187,plain,(
% 1.35/0.58    spl4_14 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.35/0.58  fof(f196,plain,(
% 1.35/0.58    ( ! [X0] : (r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | r2_hidden(sK0,X0)) ) | ~spl4_14),
% 1.35/0.58    inference(forward_demodulation,[],[f191,f93])).
% 1.35/0.58  fof(f93,plain,(
% 1.35/0.58    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.58    inference(resolution,[],[f35,f24])).
% 1.35/0.58  fof(f24,plain,(
% 1.35/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f7])).
% 1.35/0.58  fof(f7,axiom,(
% 1.35/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.58  fof(f35,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.35/0.58    inference(cnf_transformation,[],[f18])).
% 1.35/0.58  fof(f18,plain,(
% 1.35/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.35/0.58    inference(ennf_transformation,[],[f6])).
% 1.35/0.58  fof(f6,axiom,(
% 1.35/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.35/0.58  fof(f191,plain,(
% 1.35/0.58    ( ! [X0] : (r2_hidden(sK0,X0) | r2_hidden(sK0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)))) ) | ~spl4_14),
% 1.35/0.58    inference(resolution,[],[f189,f60])).
% 1.35/0.58  fof(f60,plain,(
% 1.35/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.35/0.58    inference(equality_resolution,[],[f54])).
% 1.35/0.58  fof(f54,plain,(
% 1.35/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.35/0.58    inference(definition_unfolding,[],[f43,f30])).
% 1.35/0.58  fof(f30,plain,(
% 1.35/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.35/0.58    inference(cnf_transformation,[],[f5])).
% 1.35/0.58  fof(f5,axiom,(
% 1.35/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.35/0.58  fof(f43,plain,(
% 1.35/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.35/0.58    inference(cnf_transformation,[],[f3])).
% 1.35/0.58  fof(f3,axiom,(
% 1.35/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.35/0.58  fof(f189,plain,(
% 1.35/0.58    r2_hidden(sK0,k1_xboole_0) | ~spl4_14),
% 1.35/0.58    inference(avatar_component_clause,[],[f187])).
% 1.35/0.58  fof(f190,plain,(
% 1.35/0.58    spl4_14 | ~spl4_2 | ~spl4_8),
% 1.35/0.58    inference(avatar_split_clause,[],[f170,f152,f69,f187])).
% 1.35/0.58  fof(f69,plain,(
% 1.35/0.58    spl4_2 <=> r2_hidden(sK0,sK1)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.35/0.58  fof(f152,plain,(
% 1.35/0.58    spl4_8 <=> k1_xboole_0 = sK1),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.35/0.58  fof(f170,plain,(
% 1.35/0.58    r2_hidden(sK0,k1_xboole_0) | (~spl4_2 | ~spl4_8)),
% 1.35/0.58    inference(backward_demodulation,[],[f71,f154])).
% 1.35/0.58  fof(f154,plain,(
% 1.35/0.58    k1_xboole_0 = sK1 | ~spl4_8),
% 1.35/0.58    inference(avatar_component_clause,[],[f152])).
% 1.35/0.58  fof(f71,plain,(
% 1.35/0.58    r2_hidden(sK0,sK1) | ~spl4_2),
% 1.35/0.58    inference(avatar_component_clause,[],[f69])).
% 1.35/0.58  fof(f155,plain,(
% 1.35/0.58    spl4_1 | spl4_8 | ~spl4_4),
% 1.35/0.58    inference(avatar_split_clause,[],[f148,f84,f152,f64])).
% 1.35/0.58  fof(f64,plain,(
% 1.35/0.58    spl4_1 <=> m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.35/0.58  fof(f84,plain,(
% 1.35/0.58    spl4_4 <=> m1_subset_1(sK0,sK1)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.35/0.58  fof(f148,plain,(
% 1.35/0.58    k1_xboole_0 = sK1 | m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1)) | ~spl4_4),
% 1.35/0.58    inference(resolution,[],[f53,f86])).
% 1.35/0.58  fof(f86,plain,(
% 1.35/0.58    m1_subset_1(sK0,sK1) | ~spl4_4),
% 1.35/0.58    inference(avatar_component_clause,[],[f84])).
% 1.35/0.58  fof(f53,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k3_enumset1(X1,X1,X1,X1,X1),k1_zfmisc_1(X0))) )),
% 1.35/0.58    inference(definition_unfolding,[],[f36,f51])).
% 1.35/0.58  fof(f51,plain,(
% 1.35/0.58    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.35/0.58    inference(definition_unfolding,[],[f25,f50])).
% 1.35/0.58  fof(f50,plain,(
% 1.35/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.35/0.58    inference(definition_unfolding,[],[f29,f49])).
% 1.35/0.58  fof(f49,plain,(
% 1.35/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.35/0.58    inference(definition_unfolding,[],[f37,f48])).
% 1.35/0.58  fof(f48,plain,(
% 1.35/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f11])).
% 1.35/0.58  fof(f11,axiom,(
% 1.35/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.35/0.58  fof(f37,plain,(
% 1.35/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f10])).
% 1.35/0.58  fof(f10,axiom,(
% 1.35/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.35/0.58  fof(f29,plain,(
% 1.35/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f9])).
% 1.35/0.58  fof(f9,axiom,(
% 1.35/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.58  fof(f25,plain,(
% 1.35/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f8])).
% 1.35/0.58  fof(f8,axiom,(
% 1.35/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.35/0.58  fof(f36,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))) )),
% 1.35/0.58    inference(cnf_transformation,[],[f20])).
% 1.35/0.58  fof(f20,plain,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 1.35/0.58    inference(flattening,[],[f19])).
% 1.35/0.58  fof(f19,plain,(
% 1.35/0.58    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 1.35/0.58    inference(ennf_transformation,[],[f13])).
% 1.35/0.58  fof(f13,axiom,(
% 1.35/0.58    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 1.35/0.58  fof(f124,plain,(
% 1.35/0.58    spl4_5 | ~spl4_6),
% 1.35/0.58    inference(avatar_split_clause,[],[f123,f119,f115])).
% 1.35/0.58  fof(f119,plain,(
% 1.35/0.58    spl4_6 <=> ! [X0] : ~r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0)),
% 1.35/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.35/0.58  fof(f123,plain,(
% 1.35/0.58    v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl4_6),
% 1.35/0.58    inference(resolution,[],[f120,f26])).
% 1.35/0.58  fof(f26,plain,(
% 1.35/0.58    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f2])).
% 1.35/0.58  fof(f120,plain,(
% 1.35/0.58    ( ! [X0] : (~r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0)) ) | ~spl4_6),
% 1.35/0.58    inference(avatar_component_clause,[],[f119])).
% 1.35/0.58  fof(f121,plain,(
% 1.35/0.58    spl4_5 | spl4_6),
% 1.35/0.58    inference(avatar_split_clause,[],[f113,f119,f115])).
% 1.35/0.58  fof(f113,plain,(
% 1.35/0.58    ( ! [X0] : (~r2_hidden(sK2(k5_xboole_0(k1_xboole_0,k1_xboole_0)),X0) | v1_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 1.35/0.58    inference(resolution,[],[f106,f26])).
% 1.35/0.58  fof(f106,plain,(
% 1.35/0.58    ( ! [X8,X9] : (~r2_hidden(X9,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X9,X8)) )),
% 1.35/0.58    inference(superposition,[],[f61,f93])).
% 1.35/0.58  fof(f61,plain,(
% 1.35/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.35/0.58    inference(equality_resolution,[],[f55])).
% 1.35/0.58  fof(f55,plain,(
% 1.35/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.35/0.58    inference(definition_unfolding,[],[f42,f30])).
% 1.35/0.58  fof(f42,plain,(
% 1.35/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.35/0.58    inference(cnf_transformation,[],[f3])).
% 1.35/0.58  fof(f87,plain,(
% 1.35/0.58    spl4_4 | ~spl4_2),
% 1.35/0.58    inference(avatar_split_clause,[],[f81,f69,f84])).
% 1.35/0.58  fof(f81,plain,(
% 1.35/0.58    m1_subset_1(sK0,sK1) | ~spl4_2),
% 1.35/0.58    inference(resolution,[],[f73,f71])).
% 1.35/0.58  fof(f73,plain,(
% 1.35/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.35/0.58    inference(global_subsumption,[],[f27,f33])).
% 1.35/0.58  fof(f33,plain,(
% 1.35/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.35/0.58    inference(cnf_transformation,[],[f17])).
% 1.35/0.58  fof(f17,plain,(
% 1.35/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.35/0.58    inference(ennf_transformation,[],[f12])).
% 1.35/0.58  fof(f12,axiom,(
% 1.35/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.35/0.58  fof(f72,plain,(
% 1.35/0.58    spl4_2),
% 1.35/0.58    inference(avatar_split_clause,[],[f22,f69])).
% 1.35/0.58  fof(f22,plain,(
% 1.35/0.58    r2_hidden(sK0,sK1)),
% 1.35/0.58    inference(cnf_transformation,[],[f16])).
% 1.35/0.58  fof(f16,plain,(
% 1.35/0.58    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 1.35/0.58    inference(ennf_transformation,[],[f15])).
% 1.35/0.58  fof(f15,negated_conjecture,(
% 1.35/0.58    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.35/0.58    inference(negated_conjecture,[],[f14])).
% 1.35/0.58  fof(f14,conjecture,(
% 1.35/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.35/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 1.35/0.58  fof(f67,plain,(
% 1.35/0.58    ~spl4_1),
% 1.35/0.58    inference(avatar_split_clause,[],[f52,f64])).
% 1.35/0.58  fof(f52,plain,(
% 1.35/0.58    ~m1_subset_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_zfmisc_1(sK1))),
% 1.35/0.58    inference(definition_unfolding,[],[f23,f51])).
% 1.35/0.58  fof(f23,plain,(
% 1.35/0.58    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 1.35/0.58    inference(cnf_transformation,[],[f16])).
% 1.35/0.58  % SZS output end Proof for theBenchmark
% 1.35/0.58  % (10031)------------------------------
% 1.35/0.58  % (10031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (10031)Termination reason: Refutation
% 1.35/0.58  
% 1.35/0.58  % (10031)Memory used [KB]: 10746
% 1.35/0.58  % (10031)Time elapsed: 0.167 s
% 1.35/0.58  % (10031)------------------------------
% 1.35/0.58  % (10031)------------------------------
% 1.35/0.58  % (10037)Refutation not found, incomplete strategy% (10037)------------------------------
% 1.35/0.58  % (10037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.58  % (10037)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.58  
% 1.35/0.58  % (10037)Memory used [KB]: 10746
% 1.35/0.58  % (10037)Time elapsed: 0.147 s
% 1.35/0.58  % (10037)------------------------------
% 1.35/0.58  % (10037)------------------------------
% 1.35/0.58  % (10008)Success in time 0.216 s
%------------------------------------------------------------------------------
