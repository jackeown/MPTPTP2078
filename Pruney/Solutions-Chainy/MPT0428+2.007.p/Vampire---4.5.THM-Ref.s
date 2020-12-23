%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:42 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 154 expanded)
%              Number of leaves         :   20 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  225 ( 400 expanded)
%              Number of equality atoms :   39 (  91 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f55,f61,f80,f86,f97,f102,f110,f115,f120,f127,f134,f138])).

fof(f138,plain,
    ( spl2_9
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl2_9
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f136,f114])).

fof(f114,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_9
  <=> r1_tarski(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f136,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f135,f28])).

fof(f28,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f135,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(sK0)))
    | ~ spl2_12 ),
    inference(resolution,[],[f133,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f133,plain,
    ( r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl2_12
  <=> r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f134,plain,
    ( spl2_12
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f129,f124,f131])).

fof(f124,plain,
    ( spl2_11
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f129,plain,
    ( r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f128,f27])).

fof(f27,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f128,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_11 ),
    inference(resolution,[],[f126,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f126,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,
    ( spl2_11
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f122,f117,f107,f124])).

fof(f107,plain,
    ( spl2_8
  <=> k5_setfam_1(sK0,sK1) = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f117,plain,
    ( spl2_10
  <=> m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f122,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f119,f109])).

fof(f109,plain,
    ( k5_setfam_1(sK0,sK1) = k3_tarski(sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f119,plain,
    ( m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f120,plain,
    ( spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f81,f41,f117])).

fof(f41,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f81,plain,
    ( m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f115,plain,
    ( ~ spl2_9
    | spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f105,f99,f77,f112])).

fof(f77,plain,
    ( spl2_5
  <=> sK0 = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f99,plain,
    ( spl2_7
  <=> r1_tarski(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f105,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK0)
    | spl2_5
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f104,f78])).

fof(f78,plain,
    ( sK0 != k3_tarski(sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f104,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK0)
    | sK0 = k3_tarski(sK1)
    | ~ spl2_7 ),
    inference(resolution,[],[f101,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f101,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f110,plain,
    ( spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f74,f41,f107])).

fof(f74,plain,
    ( k5_setfam_1(sK0,sK1) = k3_tarski(sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f31,f43])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f102,plain,
    ( spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f88,f48,f99])).

fof(f48,plain,
    ( spl2_2
  <=> m1_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f88,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_setfam_1(X1,X0)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f50,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f97,plain,
    ( ~ spl2_1
    | spl2_3
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl2_1
    | spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f87,f53])).

fof(f53,plain,
    ( sK0 != k5_setfam_1(sK0,sK1)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

% (1811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f52,plain,
    ( spl2_3
  <=> sK0 = k5_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f87,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f74,f79])).

fof(f79,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f86,plain,
    ( spl2_2
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f83,f49])).

fof(f49,plain,
    ( ~ m1_setfam_1(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f83,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(superposition,[],[f45,f79])).

fof(f45,plain,(
    ! [X0] : m1_setfam_1(X0,k3_tarski(X0)) ),
    inference(resolution,[],[f37,f38])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(X1))
      | m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f75,f52,f41,f77])).

fof(f75,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f74,f54])).

fof(f54,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f61,plain,
    ( ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f60,f52,f48])).

fof(f60,plain,
    ( ~ m1_setfam_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f26,f54])).

fof(f26,plain,
    ( sK0 != k5_setfam_1(sK0,sK1)
    | ~ m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( sK0 != k5_setfam_1(sK0,sK1)
      | ~ m1_setfam_1(sK1,sK0) )
    & ( sK0 = k5_setfam_1(sK0,sK1)
      | m1_setfam_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( k5_setfam_1(X0,X1) != X0
          | ~ m1_setfam_1(X1,X0) )
        & ( k5_setfam_1(X0,X1) = X0
          | m1_setfam_1(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( sK0 != k5_setfam_1(sK0,sK1)
        | ~ m1_setfam_1(sK1,sK0) )
      & ( sK0 = k5_setfam_1(sK0,sK1)
        | m1_setfam_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <~> k5_setfam_1(X0,X1) = X0 )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( m1_setfam_1(X1,X0)
        <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f55,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f25,f52,f48])).

fof(f25,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:46:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.21/0.52  % (1810)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.21/0.52  % (1829)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.21/0.53  % (1810)Refutation found. Thanks to Tanya!
% 1.21/0.53  % SZS status Theorem for theBenchmark
% 1.21/0.53  % SZS output start Proof for theBenchmark
% 1.21/0.53  fof(f139,plain,(
% 1.21/0.53    $false),
% 1.21/0.53    inference(avatar_sat_refutation,[],[f44,f55,f61,f80,f86,f97,f102,f110,f115,f120,f127,f134,f138])).
% 1.21/0.53  fof(f138,plain,(
% 1.21/0.53    spl2_9 | ~spl2_12),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f137])).
% 1.21/0.53  fof(f137,plain,(
% 1.21/0.53    $false | (spl2_9 | ~spl2_12)),
% 1.21/0.53    inference(subsumption_resolution,[],[f136,f114])).
% 1.21/0.53  fof(f114,plain,(
% 1.21/0.53    ~r1_tarski(k3_tarski(sK1),sK0) | spl2_9),
% 1.21/0.53    inference(avatar_component_clause,[],[f112])).
% 1.21/0.53  fof(f112,plain,(
% 1.21/0.53    spl2_9 <=> r1_tarski(k3_tarski(sK1),sK0)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.21/0.53  fof(f136,plain,(
% 1.21/0.53    r1_tarski(k3_tarski(sK1),sK0) | ~spl2_12),
% 1.21/0.53    inference(forward_demodulation,[],[f135,f28])).
% 1.21/0.53  fof(f28,plain,(
% 1.21/0.53    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.21/0.53    inference(cnf_transformation,[],[f3])).
% 1.21/0.53  fof(f3,axiom,(
% 1.21/0.53    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.21/0.53  fof(f135,plain,(
% 1.21/0.53    r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(sK0))) | ~spl2_12),
% 1.21/0.53    inference(resolution,[],[f133,f29])).
% 1.21/0.53  fof(f29,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f12])).
% 1.21/0.53  fof(f12,plain,(
% 1.21/0.53    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f2])).
% 1.21/0.53  fof(f2,axiom,(
% 1.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.21/0.53  fof(f133,plain,(
% 1.21/0.53    r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_12),
% 1.21/0.53    inference(avatar_component_clause,[],[f131])).
% 1.21/0.53  fof(f131,plain,(
% 1.21/0.53    spl2_12 <=> r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.21/0.53  fof(f134,plain,(
% 1.21/0.53    spl2_12 | ~spl2_11),
% 1.21/0.53    inference(avatar_split_clause,[],[f129,f124,f131])).
% 1.21/0.53  fof(f124,plain,(
% 1.21/0.53    spl2_11 <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.21/0.53  fof(f129,plain,(
% 1.21/0.53    r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_11),
% 1.21/0.53    inference(subsumption_resolution,[],[f128,f27])).
% 1.21/0.53  fof(f27,plain,(
% 1.21/0.53    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f4])).
% 1.21/0.53  fof(f4,axiom,(
% 1.21/0.53    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.21/0.53  fof(f128,plain,(
% 1.21/0.53    v1_xboole_0(k1_zfmisc_1(sK0)) | r2_hidden(k3_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_11),
% 1.21/0.53    inference(resolution,[],[f126,f30])).
% 1.21/0.53  fof(f30,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f14])).
% 1.21/0.53  fof(f14,plain,(
% 1.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.21/0.53    inference(flattening,[],[f13])).
% 1.21/0.53  fof(f13,plain,(
% 1.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.21/0.53    inference(ennf_transformation,[],[f8])).
% 1.21/0.53  fof(f8,axiom,(
% 1.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.21/0.53  fof(f126,plain,(
% 1.21/0.53    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_11),
% 1.21/0.53    inference(avatar_component_clause,[],[f124])).
% 1.21/0.53  fof(f127,plain,(
% 1.21/0.53    spl2_11 | ~spl2_8 | ~spl2_10),
% 1.21/0.53    inference(avatar_split_clause,[],[f122,f117,f107,f124])).
% 1.21/0.53  fof(f107,plain,(
% 1.21/0.53    spl2_8 <=> k5_setfam_1(sK0,sK1) = k3_tarski(sK1)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.21/0.53  fof(f117,plain,(
% 1.21/0.53    spl2_10 <=> m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.21/0.53  fof(f122,plain,(
% 1.21/0.53    m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) | (~spl2_8 | ~spl2_10)),
% 1.21/0.53    inference(forward_demodulation,[],[f119,f109])).
% 1.21/0.53  fof(f109,plain,(
% 1.21/0.53    k5_setfam_1(sK0,sK1) = k3_tarski(sK1) | ~spl2_8),
% 1.21/0.53    inference(avatar_component_clause,[],[f107])).
% 1.21/0.53  fof(f119,plain,(
% 1.21/0.53    m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_10),
% 1.21/0.53    inference(avatar_component_clause,[],[f117])).
% 1.21/0.53  fof(f120,plain,(
% 1.21/0.53    spl2_10 | ~spl2_1),
% 1.21/0.53    inference(avatar_split_clause,[],[f81,f41,f117])).
% 1.21/0.53  fof(f41,plain,(
% 1.21/0.53    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.21/0.53  fof(f81,plain,(
% 1.21/0.53    m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_1),
% 1.21/0.53    inference(resolution,[],[f32,f43])).
% 1.21/0.53  fof(f43,plain,(
% 1.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_1),
% 1.21/0.53    inference(avatar_component_clause,[],[f41])).
% 1.21/0.53  fof(f32,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f16])).
% 1.21/0.53  fof(f16,plain,(
% 1.21/0.53    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/0.53    inference(ennf_transformation,[],[f6])).
% 1.21/0.53  fof(f6,axiom,(
% 1.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 1.21/0.53  fof(f115,plain,(
% 1.21/0.53    ~spl2_9 | spl2_5 | ~spl2_7),
% 1.21/0.53    inference(avatar_split_clause,[],[f105,f99,f77,f112])).
% 1.21/0.53  fof(f77,plain,(
% 1.21/0.53    spl2_5 <=> sK0 = k3_tarski(sK1)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.21/0.53  fof(f99,plain,(
% 1.21/0.53    spl2_7 <=> r1_tarski(sK0,k3_tarski(sK1))),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.21/0.53  fof(f105,plain,(
% 1.21/0.53    ~r1_tarski(k3_tarski(sK1),sK0) | (spl2_5 | ~spl2_7)),
% 1.21/0.53    inference(subsumption_resolution,[],[f104,f78])).
% 1.21/0.53  fof(f78,plain,(
% 1.21/0.53    sK0 != k3_tarski(sK1) | spl2_5),
% 1.21/0.53    inference(avatar_component_clause,[],[f77])).
% 1.21/0.53  fof(f104,plain,(
% 1.21/0.53    ~r1_tarski(k3_tarski(sK1),sK0) | sK0 = k3_tarski(sK1) | ~spl2_7),
% 1.21/0.53    inference(resolution,[],[f101,f35])).
% 1.21/0.53  fof(f35,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.21/0.53    inference(cnf_transformation,[],[f22])).
% 1.21/0.53  fof(f22,plain,(
% 1.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.21/0.53    inference(flattening,[],[f21])).
% 1.21/0.53  fof(f21,plain,(
% 1.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.21/0.53    inference(nnf_transformation,[],[f1])).
% 1.21/0.53  fof(f1,axiom,(
% 1.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.21/0.53  fof(f101,plain,(
% 1.21/0.53    r1_tarski(sK0,k3_tarski(sK1)) | ~spl2_7),
% 1.21/0.53    inference(avatar_component_clause,[],[f99])).
% 1.21/0.53  fof(f110,plain,(
% 1.21/0.53    spl2_8 | ~spl2_1),
% 1.21/0.53    inference(avatar_split_clause,[],[f74,f41,f107])).
% 1.21/0.53  fof(f74,plain,(
% 1.21/0.53    k5_setfam_1(sK0,sK1) = k3_tarski(sK1) | ~spl2_1),
% 1.21/0.53    inference(resolution,[],[f31,f43])).
% 1.21/0.53  fof(f31,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f15])).
% 1.21/0.53  fof(f15,plain,(
% 1.21/0.53    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/0.53    inference(ennf_transformation,[],[f7])).
% 1.21/0.53  fof(f7,axiom,(
% 1.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 1.21/0.53  fof(f102,plain,(
% 1.21/0.53    spl2_7 | ~spl2_2),
% 1.21/0.53    inference(avatar_split_clause,[],[f88,f48,f99])).
% 1.21/0.53  fof(f48,plain,(
% 1.21/0.53    spl2_2 <=> m1_setfam_1(sK1,sK0)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.21/0.53  fof(f88,plain,(
% 1.21/0.53    r1_tarski(sK0,k3_tarski(sK1)) | ~spl2_2),
% 1.21/0.53    inference(resolution,[],[f50,f36])).
% 1.21/0.53  fof(f36,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~m1_setfam_1(X1,X0) | r1_tarski(X0,k3_tarski(X1))) )),
% 1.21/0.53    inference(cnf_transformation,[],[f23])).
% 1.21/0.53  fof(f23,plain,(
% 1.21/0.53    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 1.21/0.53    inference(nnf_transformation,[],[f5])).
% 1.21/0.53  fof(f5,axiom,(
% 1.21/0.53    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 1.21/0.53  fof(f50,plain,(
% 1.21/0.53    m1_setfam_1(sK1,sK0) | ~spl2_2),
% 1.21/0.53    inference(avatar_component_clause,[],[f48])).
% 1.21/0.53  fof(f97,plain,(
% 1.21/0.53    ~spl2_1 | spl2_3 | ~spl2_5),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f96])).
% 1.21/0.53  fof(f96,plain,(
% 1.21/0.53    $false | (~spl2_1 | spl2_3 | ~spl2_5)),
% 1.21/0.53    inference(subsumption_resolution,[],[f87,f53])).
% 1.21/0.53  fof(f53,plain,(
% 1.21/0.53    sK0 != k5_setfam_1(sK0,sK1) | spl2_3),
% 1.21/0.53    inference(avatar_component_clause,[],[f52])).
% 1.21/0.53  % (1811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.21/0.53  fof(f52,plain,(
% 1.21/0.53    spl2_3 <=> sK0 = k5_setfam_1(sK0,sK1)),
% 1.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.21/0.53  fof(f87,plain,(
% 1.21/0.53    sK0 = k5_setfam_1(sK0,sK1) | (~spl2_1 | ~spl2_5)),
% 1.21/0.53    inference(forward_demodulation,[],[f74,f79])).
% 1.21/0.53  fof(f79,plain,(
% 1.21/0.53    sK0 = k3_tarski(sK1) | ~spl2_5),
% 1.21/0.53    inference(avatar_component_clause,[],[f77])).
% 1.21/0.53  fof(f86,plain,(
% 1.21/0.53    spl2_2 | ~spl2_5),
% 1.21/0.53    inference(avatar_contradiction_clause,[],[f85])).
% 1.21/0.53  fof(f85,plain,(
% 1.21/0.53    $false | (spl2_2 | ~spl2_5)),
% 1.21/0.53    inference(subsumption_resolution,[],[f83,f49])).
% 1.21/0.53  fof(f49,plain,(
% 1.21/0.53    ~m1_setfam_1(sK1,sK0) | spl2_2),
% 1.21/0.53    inference(avatar_component_clause,[],[f48])).
% 1.21/0.53  fof(f83,plain,(
% 1.21/0.53    m1_setfam_1(sK1,sK0) | ~spl2_5),
% 1.21/0.53    inference(superposition,[],[f45,f79])).
% 1.21/0.53  fof(f45,plain,(
% 1.21/0.53    ( ! [X0] : (m1_setfam_1(X0,k3_tarski(X0))) )),
% 1.21/0.53    inference(resolution,[],[f37,f38])).
% 1.21/0.53  fof(f38,plain,(
% 1.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.21/0.53    inference(equality_resolution,[],[f34])).
% 1.21/0.53  fof(f34,plain,(
% 1.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.21/0.53    inference(cnf_transformation,[],[f22])).
% 1.21/0.53  fof(f37,plain,(
% 1.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k3_tarski(X1)) | m1_setfam_1(X1,X0)) )),
% 1.21/0.53    inference(cnf_transformation,[],[f23])).
% 1.21/0.53  fof(f80,plain,(
% 1.21/0.53    spl2_5 | ~spl2_1 | ~spl2_3),
% 1.21/0.53    inference(avatar_split_clause,[],[f75,f52,f41,f77])).
% 1.21/0.53  fof(f75,plain,(
% 1.21/0.53    sK0 = k3_tarski(sK1) | (~spl2_1 | ~spl2_3)),
% 1.21/0.53    inference(forward_demodulation,[],[f74,f54])).
% 1.21/0.53  fof(f54,plain,(
% 1.21/0.53    sK0 = k5_setfam_1(sK0,sK1) | ~spl2_3),
% 1.21/0.53    inference(avatar_component_clause,[],[f52])).
% 1.21/0.53  fof(f61,plain,(
% 1.21/0.53    ~spl2_2 | ~spl2_3),
% 1.21/0.53    inference(avatar_split_clause,[],[f60,f52,f48])).
% 1.21/0.53  fof(f60,plain,(
% 1.21/0.53    ~m1_setfam_1(sK1,sK0) | ~spl2_3),
% 1.21/0.53    inference(subsumption_resolution,[],[f26,f54])).
% 1.21/0.53  fof(f26,plain,(
% 1.21/0.53    sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f20,plain,(
% 1.21/0.53    (sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)) & (sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).
% 1.21/0.53  fof(f19,plain,(
% 1.21/0.53    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)) & (sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.21/0.53    introduced(choice_axiom,[])).
% 1.21/0.53  fof(f18,plain,(
% 1.21/0.53    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/0.53    inference(flattening,[],[f17])).
% 1.21/0.53  fof(f17,plain,(
% 1.21/0.53    ? [X0,X1] : (((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/0.53    inference(nnf_transformation,[],[f11])).
% 1.21/0.53  fof(f11,plain,(
% 1.21/0.53    ? [X0,X1] : ((m1_setfam_1(X1,X0) <~> k5_setfam_1(X0,X1) = X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.21/0.53    inference(ennf_transformation,[],[f10])).
% 1.21/0.53  fof(f10,negated_conjecture,(
% 1.21/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 1.21/0.53    inference(negated_conjecture,[],[f9])).
% 1.21/0.53  fof(f9,conjecture,(
% 1.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 1.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).
% 1.21/0.53  fof(f55,plain,(
% 1.21/0.53    spl2_2 | spl2_3),
% 1.21/0.53    inference(avatar_split_clause,[],[f25,f52,f48])).
% 1.21/0.53  fof(f25,plain,(
% 1.21/0.53    sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  fof(f44,plain,(
% 1.21/0.53    spl2_1),
% 1.21/0.53    inference(avatar_split_clause,[],[f24,f41])).
% 1.21/0.53  fof(f24,plain,(
% 1.21/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.21/0.53    inference(cnf_transformation,[],[f20])).
% 1.21/0.53  % SZS output end Proof for theBenchmark
% 1.21/0.53  % (1810)------------------------------
% 1.21/0.53  % (1810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (1810)Termination reason: Refutation
% 1.21/0.53  
% 1.21/0.53  % (1810)Memory used [KB]: 6140
% 1.21/0.53  % (1810)Time elapsed: 0.095 s
% 1.21/0.53  % (1810)------------------------------
% 1.21/0.53  % (1810)------------------------------
% 1.21/0.53  % (1807)Success in time 0.17 s
%------------------------------------------------------------------------------
