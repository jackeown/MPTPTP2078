%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  85 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :  130 ( 224 expanded)
%              Number of equality atoms :   70 ( 134 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f39,f55,f62,f63,f68,f75,f79])).

fof(f79,plain,
    ( ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f77,f25])).

fof(f25,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl3_1
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,
    ( sK2 != k2_mcart_1(sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f18,f74])).

fof(f74,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_7
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f18,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k2_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f75,plain,
    ( spl3_3
    | spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f70,f23,f72,f33])).

fof(f33,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK2,k2_zfmisc_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k2_zfmisc_1(X1,X0))
        | k1_xboole_0 = X1 )
    | ~ spl3_1 ),
    inference(superposition,[],[f17,f25])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f68,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f65,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f11,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f11,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) != k1_xboole_0
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f63,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f33,f48,f44])).

fof(f48,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f40,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(resolution,[],[f34,f10])).

fof(f10,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k2_zfmisc_1(X1,X0))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f62,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f59,f21])).

fof(f21,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f11,f50])).

fof(f50,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f55,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f52,f29])).

fof(f29,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_2
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( sK2 != k1_mcart_1(sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f19,f38])).

fof(f38,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_4
  <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f19,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k1_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f31,f27,f36,f33])).

fof(f31,plain,
    ( ! [X0,X1] :
        ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k2_zfmisc_1(X1,X0))
        | k1_xboole_0 = X1 )
    | ~ spl3_2 ),
    inference(superposition,[],[f17,f29])).

fof(f30,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f9,f27,f23])).

fof(f9,plain,
    ( sK2 = k1_mcart_1(sK2)
    | sK2 = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (22009)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.42  % (22009)Refutation not found, incomplete strategy% (22009)------------------------------
% 0.21/0.42  % (22009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (22009)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (22009)Memory used [KB]: 10490
% 0.21/0.42  % (22009)Time elapsed: 0.003 s
% 0.21/0.42  % (22009)------------------------------
% 0.21/0.42  % (22009)------------------------------
% 0.21/0.45  % (21990)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (21990)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f30,f39,f55,f62,f63,f68,f75,f79])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_7),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f78])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    $false | (~spl3_1 | ~spl3_7)),
% 0.21/0.46    inference(subsumption_resolution,[],[f77,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    sK2 = k2_mcart_1(sK2) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    spl3_1 <=> sK2 = k2_mcart_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    sK2 != k2_mcart_1(sK2) | ~spl3_7),
% 0.21/0.46    inference(superposition,[],[f18,f74])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f72])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl3_7 <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.46    inference(equality_resolution,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k2_mcart_1(X0) != X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl3_3 | spl3_7 | ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f70,f23,f72,f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    spl3_3 <=> ! [X1,X0] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | ~m1_subset_1(sK2,k2_zfmisc_1(X1,X0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0,X1] : (sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1) ) | ~spl3_1),
% 0.21/0.46    inference(superposition,[],[f17,f25])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ~spl3_5),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    $false | ~spl3_5),
% 0.21/0.46    inference(subsumption_resolution,[],[f65,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(equality_resolution,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | ~spl3_5),
% 0.21/0.46    inference(backward_demodulation,[],[f11,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    k1_xboole_0 = sK1 | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl3_5 <=> k1_xboole_0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k2_zfmisc_1(X0,X1) != k1_xboole_0)),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl3_5 | spl3_6 | ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f40,f33,f48,f44])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl3_6 <=> k1_xboole_0 = sK0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl3_3),
% 0.21/0.46    inference(resolution,[],[f34,f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f33])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ~spl3_6),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    $false | ~spl3_6),
% 0.21/0.46    inference(subsumption_resolution,[],[f59,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.46    inference(equality_resolution,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | ~spl3_6),
% 0.21/0.46    inference(backward_demodulation,[],[f11,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    k1_xboole_0 = sK0 | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ~spl3_2 | ~spl3_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    $false | (~spl3_2 | ~spl3_4)),
% 0.21/0.46    inference(subsumption_resolution,[],[f52,f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    sK2 = k1_mcart_1(sK2) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    spl3_2 <=> sK2 = k1_mcart_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    sK2 != k1_mcart_1(sK2) | ~spl3_4),
% 0.21/0.46    inference(superposition,[],[f19,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    spl3_4 <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.46    inference(equality_resolution,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k1_mcart_1(X0) != X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl3_3 | spl3_4 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f27,f36,f33])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | k1_xboole_0 = X0 | ~m1_subset_1(sK2,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1) ) | ~spl3_2),
% 0.21/0.46    inference(superposition,[],[f17,f29])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    spl3_1 | spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f9,f27,f23])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    sK2 = k1_mcart_1(sK2) | sK2 = k2_mcart_1(sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21990)------------------------------
% 0.21/0.46  % (21990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21990)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21990)Memory used [KB]: 10618
% 0.21/0.46  % (21990)Time elapsed: 0.042 s
% 0.21/0.46  % (21990)------------------------------
% 0.21/0.46  % (21990)------------------------------
% 0.21/0.46  % (21999)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (21988)Success in time 0.109 s
%------------------------------------------------------------------------------
