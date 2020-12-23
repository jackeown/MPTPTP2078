%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 166 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  190 ( 389 expanded)
%              Number of equality atoms :   18 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f51,f59,f68,f94,f99,f127,f149,f174,f192,f200])).

fof(f200,plain,
    ( spl4_17
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl4_17
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f197,f173])).

fof(f173,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_17
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f197,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl4_19 ),
    inference(resolution,[],[f191,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f191,plain,
    ( r2_hidden(sK3(sK1,sK1),sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_19
  <=> r2_hidden(sK3(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f192,plain,
    ( spl4_19
    | spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f159,f146,f65,f189])).

fof(f65,plain,
    ( spl4_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f146,plain,
    ( spl4_15
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f159,plain,
    ( r2_hidden(sK3(sK1,sK1),sK1)
    | spl4_5
    | ~ spl4_15 ),
    inference(superposition,[],[f73,f148])).

fof(f148,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f146])).

fof(f73,plain,
    ( ! [X3] : r2_hidden(sK3(sK1,k4_xboole_0(sK0,X3)),sK1)
    | spl4_5 ),
    inference(resolution,[],[f69,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(sK0,X0))
    | spl4_5 ),
    inference(resolution,[],[f67,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f67,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f174,plain,
    ( ~ spl4_17
    | spl4_5
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f161,f146,f65,f171])).

fof(f161,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_5
    | ~ spl4_15 ),
    inference(superposition,[],[f69,f148])).

fof(f149,plain,
    ( spl4_15
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f131,f124,f96,f146])).

fof(f96,plain,
    ( spl4_10
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f124,plain,
    ( spl4_13
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f131,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f129,f98])).

fof(f98,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f129,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_13 ),
    inference(resolution,[],[f126,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f126,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,
    ( spl4_13
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f117,f91,f36,f124])).

fof(f36,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f91,plain,
    ( spl4_9
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f117,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f116,f38])).

fof(f38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f116,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_9 ),
    inference(superposition,[],[f21,f93])).

fof(f93,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f99,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f54,f36,f96])).

fof(f54,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f52,f53])).

fof(f53,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f38,f22])).

fof(f52,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f94,plain,
    ( spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f53,f36,f91])).

fof(f68,plain,
    ( ~ spl4_5
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f63,f56,f48,f65])).

fof(f48,plain,
    ( spl4_3
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f56,plain,
    ( spl4_4
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f63,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f60,f50])).

fof(f50,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f60,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | spl4_4 ),
    inference(resolution,[],[f58,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f58,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f59,plain,
    ( ~ spl4_4
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f46,f31,f56])).

fof(f31,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f44,f45])).

fof(f45,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f43,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | r1_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f17,f41])).

fof(f41,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f17,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f44,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f18,f41])).

fof(f18,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f45,f31,f48])).

fof(f39,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f31])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:27:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (26457)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (26473)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (26473)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f201,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f34,f39,f51,f59,f68,f94,f99,f127,f149,f174,f192,f200])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    spl4_17 | ~spl4_19),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f199])).
% 0.22/0.55  fof(f199,plain,(
% 0.22/0.55    $false | (spl4_17 | ~spl4_19)),
% 0.22/0.55    inference(subsumption_resolution,[],[f197,f173])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    ~r1_tarski(sK1,sK1) | spl4_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f171])).
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    spl4_17 <=> r1_tarski(sK1,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    r1_tarski(sK1,sK1) | ~spl4_19),
% 0.22/0.55    inference(resolution,[],[f191,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f191,plain,(
% 0.22/0.55    r2_hidden(sK3(sK1,sK1),sK1) | ~spl4_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f189])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    spl4_19 <=> r2_hidden(sK3(sK1,sK1),sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    spl4_19 | spl4_5 | ~spl4_15),
% 0.22/0.55    inference(avatar_split_clause,[],[f159,f146,f65,f189])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    spl4_5 <=> r1_tarski(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    spl4_15 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    r2_hidden(sK3(sK1,sK1),sK1) | (spl4_5 | ~spl4_15)),
% 0.22/0.55    inference(superposition,[],[f73,f148])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_15),
% 0.22/0.55    inference(avatar_component_clause,[],[f146])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X3] : (r2_hidden(sK3(sK1,k4_xboole_0(sK0,X3)),sK1)) ) | spl4_5),
% 0.22/0.55    inference(resolution,[],[f69,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(sK0,X0))) ) | spl4_5),
% 0.22/0.55    inference(resolution,[],[f67,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ~r1_tarski(sK1,sK0) | spl4_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f65])).
% 0.22/0.55  fof(f174,plain,(
% 0.22/0.55    ~spl4_17 | spl4_5 | ~spl4_15),
% 0.22/0.55    inference(avatar_split_clause,[],[f161,f146,f65,f171])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    ~r1_tarski(sK1,sK1) | (spl4_5 | ~spl4_15)),
% 0.22/0.55    inference(superposition,[],[f69,f148])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    spl4_15 | ~spl4_10 | ~spl4_13),
% 0.22/0.55    inference(avatar_split_clause,[],[f131,f124,f96,f146])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    spl4_10 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.55  fof(f124,plain,(
% 0.22/0.55    spl4_13 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl4_10 | ~spl4_13)),
% 0.22/0.55    inference(forward_demodulation,[],[f129,f98])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f96])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_13),
% 0.22/0.55    inference(resolution,[],[f126,f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl4_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f124])).
% 0.22/0.55  fof(f127,plain,(
% 0.22/0.55    spl4_13 | ~spl4_2 | ~spl4_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f117,f91,f36,f124])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    spl4_9 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl4_2 | ~spl4_9)),
% 0.22/0.55    inference(subsumption_resolution,[],[f116,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f36])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_9),
% 0.22/0.55    inference(superposition,[],[f21,f93])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f91])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    spl4_10 | ~spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f54,f36,f96])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl4_2),
% 0.22/0.55    inference(backward_demodulation,[],[f52,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_2),
% 0.22/0.55    inference(resolution,[],[f38,f22])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl4_2),
% 0.22/0.55    inference(resolution,[],[f38,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    spl4_9 | ~spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f53,f36,f91])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ~spl4_5 | ~spl4_3 | spl4_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f63,f56,f48,f65])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    spl4_3 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    spl4_4 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ~r1_tarski(sK1,sK0) | (~spl4_3 | spl4_4)),
% 0.22/0.55    inference(subsumption_resolution,[],[f60,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    r1_xboole_0(sK1,sK2) | ~spl4_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f48])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ~r1_xboole_0(sK1,sK2) | ~r1_tarski(sK1,sK0) | spl4_4),
% 0.22/0.55    inference(resolution,[],[f58,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | spl4_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f56])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ~spl4_4 | ~spl4_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f46,f31,f56])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl4_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f44,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    r1_xboole_0(sK1,sK2) | ~spl4_1),
% 0.22/0.55    inference(subsumption_resolution,[],[f43,f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | r1_xboole_0(sK1,sK2) | ~spl4_1),
% 0.22/0.55    inference(backward_demodulation,[],[f17,f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_1),
% 0.22/0.55    inference(resolution,[],[f33,f22])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f31])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f7])).
% 0.22/0.55  fof(f7,conjecture,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~r1_xboole_0(sK1,sK2) | ~spl4_1),
% 0.22/0.55    inference(backward_demodulation,[],[f18,f41])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    spl4_3 | ~spl4_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f45,f31,f48])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f20,f36])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    spl4_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f19,f31])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (26473)------------------------------
% 0.22/0.55  % (26473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (26473)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (26473)Memory used [KB]: 10874
% 0.22/0.55  % (26473)Time elapsed: 0.106 s
% 0.22/0.55  % (26473)------------------------------
% 0.22/0.55  % (26473)------------------------------
% 0.22/0.55  % (26452)Success in time 0.184 s
%------------------------------------------------------------------------------
