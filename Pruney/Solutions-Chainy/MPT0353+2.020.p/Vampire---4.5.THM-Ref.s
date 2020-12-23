%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:23 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 108 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  163 ( 231 expanded)
%              Number of equality atoms :   40 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f73,f83,f97,f102,f149,f165,f241])).

fof(f241,plain,
    ( spl4_3
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl4_3
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f238,f164])).

fof(f164,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_15
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f238,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(k3_xboole_0(sK1,sK0),sK2)
    | spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f72,f115])).

fof(f115,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k3_xboole_0(X0,sK0),sK2)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f110,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f110,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k4_xboole_0(sK0,sK2))
    | ~ spl4_7 ),
    inference(resolution,[],[f96,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f96,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_7
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f72,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_3
  <=> k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f165,plain,
    ( spl4_15
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f155,f146,f162])).

fof(f146,plain,
    ( spl4_13
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f155,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f154,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f154,plain,
    ( k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_13 ),
    inference(superposition,[],[f25,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f149,plain,
    ( spl4_13
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f119,f99,f146])).

fof(f99,plain,
    ( spl4_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f119,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f101,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f101,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f102,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f86,f80,f99])).

fof(f80,plain,
    ( spl4_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f86,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f82,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f82,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f97,plain,
    ( spl4_7
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f59,f44,f94])).

fof(f44,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f59,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f56,f55])).

fof(f55,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f46,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f56,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f46,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f83,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f68,f49,f80])).

fof(f49,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f68,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f65,f23])).

fof(f23,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

% (27502)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f65,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f51,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f73,plain,
    ( ~ spl4_3
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f66,f49,f44,f70])).

fof(f66,plain,
    ( k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f58,f62])).

fof(f62,plain,
    ( ! [X1] : k4_xboole_0(sK1,X1) = k7_subset_1(sK0,sK1,X1)
    | ~ spl4_2 ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f58,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f21,f55])).

fof(f21,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f52,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (27509)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (27525)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.19/0.51  % (27497)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.19/0.52  % (27517)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.19/0.52  % (27522)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.19/0.52  % (27500)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.53  % (27514)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.19/0.53  % (27517)Refutation found. Thanks to Tanya!
% 1.19/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % (27519)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.53  % (27511)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.53  % (27508)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.53  % (27501)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.34/0.53  % (27504)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.53  % (27515)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.53  % (27505)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f242,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(avatar_sat_refutation,[],[f47,f52,f73,f83,f97,f102,f149,f165,f241])).
% 1.34/0.54  fof(f241,plain,(
% 1.34/0.54    spl4_3 | ~spl4_7 | ~spl4_15),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f240])).
% 1.34/0.54  fof(f240,plain,(
% 1.34/0.54    $false | (spl4_3 | ~spl4_7 | ~spl4_15)),
% 1.34/0.54    inference(trivial_inequality_removal,[],[f239])).
% 1.34/0.54  fof(f239,plain,(
% 1.34/0.54    k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) | (spl4_3 | ~spl4_7 | ~spl4_15)),
% 1.34/0.54    inference(forward_demodulation,[],[f238,f164])).
% 1.34/0.54  fof(f164,plain,(
% 1.34/0.54    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_15),
% 1.34/0.54    inference(avatar_component_clause,[],[f162])).
% 1.34/0.54  fof(f162,plain,(
% 1.34/0.54    spl4_15 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.34/0.54  fof(f238,plain,(
% 1.34/0.54    k4_xboole_0(sK1,sK2) != k4_xboole_0(k3_xboole_0(sK1,sK0),sK2) | (spl4_3 | ~spl4_7)),
% 1.34/0.54    inference(superposition,[],[f72,f115])).
% 1.34/0.54  fof(f115,plain,(
% 1.34/0.54    ( ! [X0] : (k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(k3_xboole_0(X0,sK0),sK2)) ) | ~spl4_7),
% 1.34/0.54    inference(forward_demodulation,[],[f110,f38])).
% 1.34/0.54  fof(f38,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.34/0.54  fof(f110,plain,(
% 1.34/0.54    ( ! [X0] : (k9_subset_1(sK0,X0,k4_xboole_0(sK0,sK2)) = k3_xboole_0(X0,k4_xboole_0(sK0,sK2))) ) | ~spl4_7),
% 1.34/0.54    inference(resolution,[],[f96,f40])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f11])).
% 1.34/0.54  fof(f11,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.34/0.54  fof(f96,plain,(
% 1.34/0.54    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_7),
% 1.34/0.54    inference(avatar_component_clause,[],[f94])).
% 1.34/0.54  fof(f94,plain,(
% 1.34/0.54    spl4_7 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.34/0.54  fof(f72,plain,(
% 1.34/0.54    k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | spl4_3),
% 1.34/0.54    inference(avatar_component_clause,[],[f70])).
% 1.34/0.54  fof(f70,plain,(
% 1.34/0.54    spl4_3 <=> k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.34/0.54  fof(f165,plain,(
% 1.34/0.54    spl4_15 | ~spl4_13),
% 1.34/0.54    inference(avatar_split_clause,[],[f155,f146,f162])).
% 1.34/0.54  fof(f146,plain,(
% 1.34/0.54    spl4_13 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.34/0.54  fof(f155,plain,(
% 1.34/0.54    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_13),
% 1.34/0.54    inference(forward_demodulation,[],[f154,f24])).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.34/0.54  fof(f154,plain,(
% 1.34/0.54    k3_xboole_0(sK1,sK0) = k4_xboole_0(sK1,k1_xboole_0) | ~spl4_13),
% 1.34/0.54    inference(superposition,[],[f25,f148])).
% 1.34/0.54  fof(f148,plain,(
% 1.34/0.54    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl4_13),
% 1.34/0.54    inference(avatar_component_clause,[],[f146])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.34/0.54  fof(f149,plain,(
% 1.34/0.54    spl4_13 | ~spl4_8),
% 1.34/0.54    inference(avatar_split_clause,[],[f119,f99,f146])).
% 1.34/0.54  fof(f99,plain,(
% 1.34/0.54    spl4_8 <=> r1_tarski(sK1,sK0)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.34/0.54  fof(f119,plain,(
% 1.34/0.54    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl4_8),
% 1.34/0.54    inference(resolution,[],[f101,f36])).
% 1.34/0.54  fof(f36,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.34/0.54  fof(f101,plain,(
% 1.34/0.54    r1_tarski(sK1,sK0) | ~spl4_8),
% 1.34/0.54    inference(avatar_component_clause,[],[f99])).
% 1.34/0.54  fof(f102,plain,(
% 1.34/0.54    spl4_8 | ~spl4_5),
% 1.34/0.54    inference(avatar_split_clause,[],[f86,f80,f99])).
% 1.34/0.54  fof(f80,plain,(
% 1.34/0.54    spl4_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.34/0.54  fof(f86,plain,(
% 1.34/0.54    r1_tarski(sK1,sK0) | ~spl4_5),
% 1.34/0.54    inference(resolution,[],[f82,f41])).
% 1.34/0.54  fof(f41,plain,(
% 1.34/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.34/0.54    inference(equality_resolution,[],[f33])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.34/0.54  fof(f82,plain,(
% 1.34/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_5),
% 1.34/0.54    inference(avatar_component_clause,[],[f80])).
% 1.34/0.54  fof(f97,plain,(
% 1.34/0.54    spl4_7 | ~spl4_1),
% 1.34/0.54    inference(avatar_split_clause,[],[f59,f44,f94])).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_1),
% 1.34/0.54    inference(forward_demodulation,[],[f56,f55])).
% 1.34/0.54  fof(f55,plain,(
% 1.34/0.54    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_1),
% 1.34/0.54    inference(resolution,[],[f46,f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_1),
% 1.34/0.54    inference(avatar_component_clause,[],[f44])).
% 1.34/0.54  fof(f56,plain,(
% 1.34/0.54    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl4_1),
% 1.34/0.54    inference(resolution,[],[f46,f30])).
% 1.34/0.54  fof(f30,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,plain,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.34/0.54  fof(f83,plain,(
% 1.34/0.54    spl4_5 | ~spl4_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f68,f49,f80])).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    spl4_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.34/0.54  fof(f68,plain,(
% 1.34/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.34/0.54    inference(subsumption_resolution,[],[f65,f23])).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f9])).
% 1.34/0.54  % (27502)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.34/0.54    inference(resolution,[],[f51,f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f15])).
% 1.34/0.54  fof(f15,plain,(
% 1.34/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.34/0.54    inference(avatar_component_clause,[],[f49])).
% 1.34/0.54  fof(f73,plain,(
% 1.34/0.54    ~spl4_3 | ~spl4_1 | ~spl4_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f66,f49,f44,f70])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | (~spl4_1 | ~spl4_2)),
% 1.34/0.54    inference(backward_demodulation,[],[f58,f62])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ( ! [X1] : (k4_xboole_0(sK1,X1) = k7_subset_1(sK0,sK1,X1)) ) | ~spl4_2),
% 1.34/0.54    inference(resolution,[],[f51,f39])).
% 1.34/0.54  fof(f39,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.34/0.54  fof(f58,plain,(
% 1.34/0.54    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k4_xboole_0(sK0,sK2)) | ~spl4_1),
% 1.34/0.54    inference(backward_demodulation,[],[f21,f55])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.34/0.54    inference(cnf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,plain,(
% 1.34/0.54    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.54    inference(ennf_transformation,[],[f13])).
% 1.34/0.54  fof(f13,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.34/0.54    inference(negated_conjecture,[],[f12])).
% 1.34/0.54  fof(f12,conjecture,(
% 1.34/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    spl4_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f22,f49])).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.34/0.54    inference(cnf_transformation,[],[f14])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    spl4_1),
% 1.34/0.54    inference(avatar_split_clause,[],[f20,f44])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.34/0.54    inference(cnf_transformation,[],[f14])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (27517)------------------------------
% 1.34/0.54  % (27517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (27517)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (27517)Memory used [KB]: 10874
% 1.34/0.54  % (27517)Time elapsed: 0.119 s
% 1.34/0.54  % (27517)------------------------------
% 1.34/0.54  % (27517)------------------------------
% 1.34/0.54  % (27514)Refutation not found, incomplete strategy% (27514)------------------------------
% 1.34/0.54  % (27514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (27514)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (27514)Memory used [KB]: 10618
% 1.34/0.54  % (27514)Time elapsed: 0.137 s
% 1.34/0.54  % (27514)------------------------------
% 1.34/0.54  % (27514)------------------------------
% 1.34/0.54  % (27491)Success in time 0.179 s
%------------------------------------------------------------------------------
