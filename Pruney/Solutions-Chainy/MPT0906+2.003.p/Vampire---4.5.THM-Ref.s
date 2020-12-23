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
% DateTime   : Thu Dec  3 12:59:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 103 expanded)
%              Number of leaves         :   16 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  157 ( 239 expanded)
%              Number of equality atoms :   55 (  94 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f46,f53,f60,f65,f78,f86,f91])).

fof(f91,plain,
    ( ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f88,f42])).

fof(f42,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_3
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f88,plain,
    ( sK2 != k2_mcart_1(sK2)
    | ~ spl3_9 ),
    inference(superposition,[],[f29,f85])).

fof(f85,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_9
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f29,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k2_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f86,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f82,f48,f41,f84])).

fof(f48,plain,
    ( spl3_5
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f67,f42])).

fof(f67,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f66,f27])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f66,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f49,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f49,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f78,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f69,f71])).

fof(f71,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f21,f59])).

fof(f59,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_7
  <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f21,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f69,plain,
    ( sK2 != k1_mcart_1(sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f30,f59])).

fof(f30,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k1_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,
    ( spl3_2
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f62,f37])).

fof(f37,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f61,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k2_zfmisc_1(sK0,sK1) = X0 )
    | ~ spl3_6 ),
    inference(resolution,[],[f52,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f52,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_6
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f60,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f56,f48,f44,f58])).

fof(f44,plain,
    ( spl3_4
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f56,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f55,f45])).

fof(f45,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f55,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f54,f27])).

fof(f54,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_5 ),
    inference(resolution,[],[f49,f20])).

fof(f53,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f39,f32,f51,f48])).

fof(f32,plain,
    ( spl3_1
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f33,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f46,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f17,f44,f41])).

fof(f17,plain,
    ( sK2 = k1_mcart_1(sK2)
    | sK2 = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
       => ! [X2] :
            ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
           => ( k2_mcart_1(X2) != X2
              & k1_mcart_1(X2) != X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
     => ! [X2] :
          ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
         => ( k2_mcart_1(X2) != X2
            & k1_mcart_1(X2) != X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).

fof(f38,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f36])).

fof(f19,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (13201)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (13201)Refutation not found, incomplete strategy% (13201)------------------------------
% 0.22/0.50  % (13201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (13201)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (13201)Memory used [KB]: 10618
% 0.22/0.50  % (13201)Time elapsed: 0.073 s
% 0.22/0.50  % (13201)------------------------------
% 0.22/0.50  % (13201)------------------------------
% 0.22/0.50  % (13199)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (13199)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f34,f38,f46,f53,f60,f65,f78,f86,f91])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~spl3_3 | ~spl3_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    $false | (~spl3_3 | ~spl3_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    sK2 = k2_mcart_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    spl3_3 <=> sK2 = k2_mcart_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    sK2 != k2_mcart_1(sK2) | ~spl3_9),
% 0.22/0.50    inference(superposition,[],[f29,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl3_9 <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.22/0.50    inference(equality_resolution,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k2_mcart_1(X0) != X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl3_9 | ~spl3_3 | ~spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f82,f48,f41,f84])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    spl3_5 <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | (~spl3_3 | ~spl3_5)),
% 0.22/0.50    inference(forward_demodulation,[],[f67,f42])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.22/0.50    inference(subsumption_resolution,[],[f66,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.22/0.50    inference(resolution,[],[f49,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f48])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~spl3_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    $false | ~spl3_7),
% 0.22/0.50    inference(subsumption_resolution,[],[f69,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    sK2 = k1_mcart_1(sK2) | ~spl3_7),
% 0.22/0.50    inference(superposition,[],[f21,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl3_7 <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    sK2 != k1_mcart_1(sK2) | ~spl3_7),
% 0.22/0.50    inference(superposition,[],[f30,f59])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.22/0.50    inference(equality_resolution,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k1_mcart_1(X0) != X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_2 | ~spl3_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    $false | (spl3_2 | ~spl3_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f62,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    spl3_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_6),
% 0.22/0.50    inference(resolution,[],[f61,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k2_zfmisc_1(sK0,sK1) = X0) ) | ~spl3_6),
% 0.22/0.50    inference(resolution,[],[f52,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl3_6 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_7 | ~spl3_4 | ~spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f56,f48,f44,f58])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    spl3_4 <=> sK2 = k1_mcart_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | (~spl3_4 | ~spl3_5)),
% 0.22/0.50    inference(forward_demodulation,[],[f55,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    sK2 = k1_mcart_1(sK2) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f44])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.22/0.50    inference(subsumption_resolution,[],[f54,f27])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_5),
% 0.22/0.50    inference(resolution,[],[f49,f20])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl3_5 | spl3_6 | ~spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f32,f51,f48])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    spl3_1 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_1),
% 0.22/0.50    inference(resolution,[],[f33,f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f32])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    spl3_3 | spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f44,f41])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    sK2 = k1_mcart_1(sK2) | sK2 = k2_mcart_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != k2_zfmisc_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) => ! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_mcart_1)).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f36])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f32])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (13199)------------------------------
% 0.22/0.51  % (13199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (13199)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (13199)Memory used [KB]: 6140
% 0.22/0.51  % (13199)Time elapsed: 0.073 s
% 0.22/0.51  % (13199)------------------------------
% 0.22/0.51  % (13199)------------------------------
% 0.22/0.51  % (13198)Success in time 0.143 s
%------------------------------------------------------------------------------
