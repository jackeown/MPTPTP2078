%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  78 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 157 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f50,f56,f198,f228,f232])).

fof(f232,plain,
    ( spl2_2
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl2_2
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f48,f39,f227,f73])).

fof(f73,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r1_tarski(X2,X3)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f36,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f227,plain,
    ( r1_xboole_0(sK1,sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl2_11
  <=> r1_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f39,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,
    ( k1_xboole_0 != sK1
    | spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f228,plain,
    ( ~ spl2_6
    | spl2_11
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f213,f42,f225,f156])).

fof(f156,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f42,plain,
    ( spl2_1
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f213,plain,
    ( r1_xboole_0(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(resolution,[],[f122,f43])).

fof(f43,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f122,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(X10,k3_subset_1(X8,X9))
      | r1_xboole_0(X10,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ),
    inference(superposition,[],[f37,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f29,f19])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f198,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f16,f158])).

fof(f158,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f56,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f17,f52])).

fof(f52,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f44,f47])).

fof(f47,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f44,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f17,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f31,f46,f42])).

fof(f31,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f14,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f14,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f30,f46,f42])).

fof(f30,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f15,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (8770)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.49  % (8777)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (8760)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (8760)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f49,f50,f56,f198,f228,f232])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    spl2_2 | ~spl2_11),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f229])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    $false | (spl2_2 | ~spl2_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f48,f39,f227,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_tarski(X2,X3) | k1_xboole_0 = X2) )),
% 0.21/0.50    inference(superposition,[],[f36,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f25,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f19])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    r1_xboole_0(sK1,sK1) | ~spl2_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f225])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    spl2_11 <=> r1_xboole_0(sK1,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl2_2 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ~spl2_6 | spl2_11 | ~spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f213,f42,f225,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl2_1 <=> r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    r1_xboole_0(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 0.21/0.50    inference(resolution,[],[f122,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (~r1_tarski(X10,k3_subset_1(X8,X9)) | r1_xboole_0(X10,X9) | ~m1_subset_1(X9,k1_zfmisc_1(X8))) )),
% 0.21/0.50    inference(superposition,[],[f37,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f20,f19])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f29,f19])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl2_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    $false | spl2_6),
% 0.21/0.50    inference(subsumption_resolution,[],[f16,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl2_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f156])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl2_1 | ~spl2_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f17,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | (spl2_1 | ~spl2_2)),
% 0.21/0.50    inference(forward_demodulation,[],[f44,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f46])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k3_subset_1(sK0,sK1)) | spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl2_1 | spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f46,f42])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.50    inference(definition_unfolding,[],[f14,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f46,f42])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.50    inference(definition_unfolding,[],[f15,f18])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8760)------------------------------
% 0.21/0.50  % (8760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8760)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8760)Memory used [KB]: 6268
% 0.21/0.50  % (8760)Time elapsed: 0.084 s
% 0.21/0.50  % (8760)------------------------------
% 0.21/0.50  % (8760)------------------------------
% 0.21/0.50  % (8745)Success in time 0.142 s
%------------------------------------------------------------------------------
