%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 229 expanded)
%              Number of equality atoms :   56 ( 116 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f71,f106])).

fof(f106,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f98,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
        | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK0
    | spl2_2 ),
    inference(superposition,[],[f42,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f32,f22])).

fof(f22,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k2_relat_1(k2_zfmisc_1(X4,X3)))
      | k2_relat_1(k2_zfmisc_1(X4,X3)) = X3 ) ),
    inference(resolution,[],[f31,f28])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f53,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X3,X2)))
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f45,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( r1_tarski(X1,X3)
          | ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            & ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f42,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_2
  <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f71,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f69,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK1
    | spl2_1 ),
    inference(superposition,[],[f38,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f55,f44])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1 ) ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(k2_zfmisc_1(X1,X2)) = X1 ) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f45,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
      | r1_tarski(X1,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_1
  <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f43,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f21,f40,f36])).

fof(f21,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:14:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (20319)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (20327)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (20327)Refutation not found, incomplete strategy% (20327)------------------------------
% 0.22/0.53  % (20327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20327)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20327)Memory used [KB]: 1535
% 0.22/0.53  % (20327)Time elapsed: 0.069 s
% 0.22/0.53  % (20327)------------------------------
% 0.22/0.53  % (20327)------------------------------
% 0.22/0.53  % (20319)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f43,f71,f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl2_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    $false | spl2_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f98,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    k1_xboole_0 != sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    (sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => ((sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | spl2_2),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f92])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    sK1 != sK1 | k1_xboole_0 = sK0 | spl2_2),
% 0.22/0.54    inference(superposition,[],[f42,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(resolution,[],[f57,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(resolution,[],[f32,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1) )),
% 0.22/0.54    inference(resolution,[],[f53,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X4,X3] : (~r1_tarski(X3,k2_relat_1(k2_zfmisc_1(X4,X3))) | k2_relat_1(k2_zfmisc_1(X4,X3)) = X3) )),
% 0.22/0.54    inference(resolution,[],[f31,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r1_tarski(X2,k2_relat_1(k2_zfmisc_1(X3,X2))) | v1_xboole_0(X3)) )),
% 0.22/0.54    inference(resolution,[],[f45,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | r1_tarski(X1,X3) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2,X3] : (r1_tarski(X1,X3) | (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) & ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))))) )),
% 0.22/0.54    inference(resolution,[],[f25,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | spl2_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    spl2_2 <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    spl2_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f70])).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    $false | spl2_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f69,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    k1_xboole_0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | spl2_1),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    sK0 != sK0 | k1_xboole_0 = sK1 | spl2_1),
% 0.22/0.54    inference(superposition,[],[f38,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1) )),
% 0.22/0.54    inference(resolution,[],[f55,f44])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1) )),
% 0.22/0.54    inference(resolution,[],[f52,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(k2_zfmisc_1(X1,X2)) = X1) )),
% 0.22/0.54    inference(resolution,[],[f31,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,k1_relat_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(resolution,[],[f45,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(X1,X3) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl2_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    spl2_1 <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ~spl2_1 | ~spl2_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f21,f40,f36])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (20319)------------------------------
% 0.22/0.54  % (20319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20319)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (20319)Memory used [KB]: 10618
% 0.22/0.54  % (20319)Time elapsed: 0.078 s
% 0.22/0.54  % (20319)------------------------------
% 0.22/0.54  % (20319)------------------------------
% 0.22/0.54  % (20308)Success in time 0.167 s
%------------------------------------------------------------------------------
