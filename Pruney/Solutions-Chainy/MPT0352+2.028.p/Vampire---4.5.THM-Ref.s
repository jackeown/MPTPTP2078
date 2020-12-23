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
% DateTime   : Thu Dec  3 12:44:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 196 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 463 expanded)
%              Number of equality atoms :   21 (  62 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f102,f146,f233])).

% (8415)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f233,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f147,f220,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f220,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f218,f170])).

fof(f170,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f71,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f37,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f67,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f67,plain,(
    r1_tarski(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f26,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

% (8413)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f44,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f218,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f75,f214,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f214,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f211,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f211,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f167,f178])).

fof(f178,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f79,f46])).

fof(f79,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f75,f45])).

fof(f167,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f91,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f91,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_2
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f75,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f60,f47])).

fof(f60,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f27,f36])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f147,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK2))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f88,f47])).

fof(f88,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f146,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f123,f130,f47])).

fof(f130,plain,(
    r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f56,f36])).

fof(f56,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f49,f50])).

fof(f50,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f26,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f49,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f123,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f119,f92,f30])).

fof(f92,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f119,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(X0,sK2),sK1)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f105,f39])).

% (8425)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f105,plain,
    ( ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f87,f31])).

fof(f87,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f102,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f64,f90,f86])).

fof(f64,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f54,f59])).

fof(f59,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f27,f28])).

fof(f54,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f24,f50])).

fof(f24,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f63,f90,f86])).

fof(f63,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f55,f59])).

fof(f55,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(backward_demodulation,[],[f25,f50])).

fof(f25,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:39:05 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.49  % (8414)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.49  % (8407)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.49  % (8408)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (8398)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (8419)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.50  % (8401)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.50  % (8416)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.50  % (8412)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.50  % (8399)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.50  % (8422)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.51  % (8411)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.51  % (8402)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (8420)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.51  % (8400)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (8396)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (8405)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.52  % (8403)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (8424)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (8400)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % (8410)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (8397)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (8421)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f234,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(avatar_sat_refutation,[],[f93,f102,f146,f233])).
% 0.19/0.53  % (8415)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  fof(f233,plain,(
% 0.19/0.53    spl4_1 | ~spl4_2),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f223])).
% 0.19/0.53  fof(f223,plain,(
% 0.19/0.53    $false | (spl4_1 | ~spl4_2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f147,f220,f48])).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.53    inference(equality_resolution,[],[f40])).
% 0.19/0.53  fof(f40,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f8,axiom,(
% 0.19/0.53    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.19/0.53  fof(f220,plain,(
% 0.19/0.53    r1_tarski(sK1,sK2) | ~spl4_2),
% 0.19/0.53    inference(forward_demodulation,[],[f218,f170])).
% 0.19/0.53  fof(f170,plain,(
% 0.19/0.53    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.19/0.53    inference(superposition,[],[f71,f46])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.19/0.53    inference(definition_unfolding,[],[f38,f37,f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.53  fof(f38,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.53  fof(f71,plain,(
% 0.19/0.53    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f67,f45])).
% 0.19/0.53  fof(f45,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.19/0.53    inference(definition_unfolding,[],[f32,f37])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.53  fof(f67,plain,(
% 0.19/0.53    r1_tarski(sK2,sK0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f51,f47])).
% 0.19/0.53  fof(f47,plain,(
% 0.19/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 0.19/0.53    inference(equality_resolution,[],[f41])).
% 0.19/0.53  fof(f41,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.19/0.53    inference(cnf_transformation,[],[f8])).
% 0.19/0.53  fof(f51,plain,(
% 0.19/0.53    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f26,f36])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,axiom,(
% 0.19/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  % (8413)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.53  fof(f15,plain,(
% 0.19/0.53    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f14])).
% 0.19/0.53  fof(f14,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.19/0.53    inference(negated_conjecture,[],[f13])).
% 0.19/0.53  fof(f13,conjecture,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f12])).
% 0.19/0.53  fof(f12,axiom,(
% 0.19/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.19/0.53  fof(f218,plain,(
% 0.19/0.53    r1_tarski(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | ~spl4_2),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f75,f214,f30])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f19])).
% 0.19/0.53  fof(f19,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(flattening,[],[f18])).
% 0.19/0.53  fof(f18,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.19/0.53  fof(f214,plain,(
% 0.19/0.53    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_2),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f211,f39])).
% 0.19/0.53  fof(f39,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f23])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.19/0.53  fof(f211,plain,(
% 0.19/0.53    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) | ~spl4_2),
% 0.19/0.53    inference(superposition,[],[f167,f178])).
% 0.19/0.53  fof(f178,plain,(
% 0.19/0.53    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.53    inference(superposition,[],[f79,f46])).
% 0.19/0.53  fof(f79,plain,(
% 0.19/0.53    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f75,f45])).
% 0.19/0.53  fof(f167,plain,(
% 0.19/0.53    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(X0,k4_xboole_0(sK0,sK1)))) ) | ~spl4_2),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f91,f31])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f20])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.53    inference(ennf_transformation,[],[f6])).
% 0.19/0.53  fof(f6,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.19/0.53  fof(f91,plain,(
% 0.19/0.53    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f90])).
% 0.19/0.53  fof(f90,plain,(
% 0.19/0.53    spl4_2 <=> r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.53  fof(f75,plain,(
% 0.19/0.53    r1_tarski(sK1,sK0)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f60,f47])).
% 0.19/0.53  fof(f60,plain,(
% 0.19/0.53    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f27,f36])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f147,plain,(
% 0.19/0.53    ~r2_hidden(sK1,k1_zfmisc_1(sK2)) | spl4_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f88,f47])).
% 0.19/0.53  fof(f88,plain,(
% 0.19/0.53    ~r1_tarski(sK1,sK2) | spl4_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f86])).
% 0.19/0.53  fof(f86,plain,(
% 0.19/0.53    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.53  fof(f146,plain,(
% 0.19/0.53    ~spl4_1 | spl4_2),
% 0.19/0.53    inference(avatar_contradiction_clause,[],[f143])).
% 0.19/0.53  fof(f143,plain,(
% 0.19/0.53    $false | (~spl4_1 | spl4_2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f123,f130,f47])).
% 0.19/0.53  fof(f130,plain,(
% 0.19/0.53    r2_hidden(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f44,f56,f36])).
% 0.19/0.53  fof(f56,plain,(
% 0.19/0.53    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(forward_demodulation,[],[f49,f50])).
% 0.19/0.53  fof(f50,plain,(
% 0.19/0.53    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f26,f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f16])).
% 0.19/0.53  fof(f16,plain,(
% 0.19/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f10])).
% 0.19/0.53  fof(f10,axiom,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.53  fof(f49,plain,(
% 0.19/0.53    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f26,f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f17])).
% 0.19/0.53  fof(f17,plain,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.53    inference(ennf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,axiom,(
% 0.19/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.19/0.53  fof(f123,plain,(
% 0.19/0.53    ~r1_tarski(k4_xboole_0(sK0,sK2),sK0) | (~spl4_1 | spl4_2)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f119,f92,f30])).
% 0.19/0.53  fof(f92,plain,(
% 0.19/0.53    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | spl4_2),
% 0.19/0.53    inference(avatar_component_clause,[],[f90])).
% 0.19/0.53  fof(f119,plain,(
% 0.19/0.53    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,sK2),sK1)) ) | ~spl4_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f105,f39])).
% 0.19/0.53  % (8425)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  fof(f105,plain,(
% 0.19/0.53    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(X0,sK2))) ) | ~spl4_1),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f87,f31])).
% 0.19/0.53  fof(f87,plain,(
% 0.19/0.53    r1_tarski(sK1,sK2) | ~spl4_1),
% 0.19/0.53    inference(avatar_component_clause,[],[f86])).
% 0.19/0.53  fof(f102,plain,(
% 0.19/0.53    spl4_1 | spl4_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f64,f90,f86])).
% 0.19/0.53  fof(f64,plain,(
% 0.19/0.53    r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.19/0.53    inference(backward_demodulation,[],[f54,f59])).
% 0.19/0.53  fof(f59,plain,(
% 0.19/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.19/0.53    inference(unit_resulting_resolution,[],[f27,f28])).
% 0.19/0.53  fof(f54,plain,(
% 0.19/0.53    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.19/0.53    inference(backward_demodulation,[],[f24,f50])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f93,plain,(
% 0.19/0.53    ~spl4_1 | ~spl4_2),
% 0.19/0.53    inference(avatar_split_clause,[],[f63,f90,f86])).
% 0.19/0.53  fof(f63,plain,(
% 0.19/0.53    ~r1_tarski(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.19/0.53    inference(backward_demodulation,[],[f55,f59])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.19/0.53    inference(backward_demodulation,[],[f25,f50])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (8400)------------------------------
% 0.19/0.53  % (8400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (8400)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (8400)Memory used [KB]: 6268
% 0.19/0.53  % (8400)Time elapsed: 0.134 s
% 0.19/0.53  % (8400)------------------------------
% 0.19/0.53  % (8400)------------------------------
% 0.19/0.53  % (8423)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (8409)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (8404)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.54  % (8417)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.54  % (8406)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (8418)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.54  % (8413)Refutation not found, incomplete strategy% (8413)------------------------------
% 0.19/0.54  % (8413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (8413)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (8413)Memory used [KB]: 10618
% 0.19/0.54  % (8413)Time elapsed: 0.140 s
% 0.19/0.54  % (8413)------------------------------
% 0.19/0.54  % (8413)------------------------------
% 0.19/0.55  % (8395)Success in time 0.202 s
%------------------------------------------------------------------------------
