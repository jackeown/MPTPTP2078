%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  68 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 155 expanded)
%              Number of equality atoms :   39 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f64,f72])).

fof(f72,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f70,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | spl2_2 ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK1
    | spl2_2 ),
    inference(superposition,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f47,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1 ) ),
    inference(resolution,[],[f44,f41])).

fof(f41,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_relat_1(k2_zfmisc_1(X3,X4)))
      | k1_relat_1(k2_zfmisc_1(X3,X4)) = X3 ) ),
    inference(resolution,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f38,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
      | v1_xboole_0(X0)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( r1_tarski(X1,X3)
          | ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            & ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1)))) ),
    inference(resolution,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f36,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_2
  <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f62,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,
    ( k1_xboole_0 = sK0
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK0
    | spl2_1 ),
    inference(superposition,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f49,f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X2,X1)))
      | k2_relat_1(k2_zfmisc_1(X2,X1)) = X1 ) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f45,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,k2_relat_1(k2_zfmisc_1(X2,X3)))
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f38,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
      | v1_xboole_0(X0)
      | r1_tarski(X1,X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl2_1
  <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f37,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f14,f34,f30])).

fof(f14,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:54:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (23361)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (23375)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (23356)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (23361)Refutation not found, incomplete strategy% (23361)------------------------------
% 0.21/0.50  % (23361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23361)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23361)Memory used [KB]: 1535
% 0.21/0.50  % (23361)Time elapsed: 0.080 s
% 0.21/0.50  % (23361)------------------------------
% 0.21/0.50  % (23361)------------------------------
% 0.21/0.50  % (23367)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (23375)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f37,f64,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl2_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    $false | spl2_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f70,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | spl2_2),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    sK0 != sK0 | k1_xboole_0 = sK1 | spl2_2),
% 0.21/0.50    inference(superposition,[],[f36,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1) )),
% 0.21/0.50    inference(resolution,[],[f47,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | k1_relat_1(k2_zfmisc_1(X1,X0)) = X1) )),
% 0.21/0.50    inference(resolution,[],[f44,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~r1_tarski(X3,k1_relat_1(k2_zfmisc_1(X3,X4))) | k1_relat_1(k2_zfmisc_1(X3,X4)) = X3) )),
% 0.21/0.50    inference(resolution,[],[f26,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,k1_relat_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(resolution,[],[f38,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | v1_xboole_0(X0) | r1_tarski(X1,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2,X3] : (r1_tarski(X1,X3) | (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) & ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(k1_relat_1(k2_zfmisc_1(X0,X1)),k2_relat_1(k2_zfmisc_1(X0,X1))))) )),
% 0.21/0.50    inference(resolution,[],[f20,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl2_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    spl2_2 <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl2_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    $false | spl2_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f62,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    k1_xboole_0 != sK0),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | spl2_1),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    sK1 != sK1 | k1_xboole_0 = sK0 | spl2_1),
% 0.21/0.50    inference(superposition,[],[f32,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(resolution,[],[f49,f19])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X0) | k2_relat_1(k2_zfmisc_1(X0,X1)) = X1) )),
% 0.21/0.50    inference(resolution,[],[f45,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X2,X1))) | k2_relat_1(k2_zfmisc_1(X2,X1)) = X1) )),
% 0.21/0.50    inference(resolution,[],[f26,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X3] : (r1_tarski(X3,k2_relat_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X2)) )),
% 0.21/0.50    inference(resolution,[],[f38,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) | v1_xboole_0(X0) | r1_tarski(X1,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    spl2_1 <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~spl2_1 | ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f34,f30])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (23375)------------------------------
% 0.21/0.50  % (23375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23375)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (23375)Memory used [KB]: 10618
% 0.21/0.50  % (23375)Time elapsed: 0.070 s
% 0.21/0.50  % (23375)------------------------------
% 0.21/0.50  % (23375)------------------------------
% 0.21/0.50  % (23352)Success in time 0.137 s
%------------------------------------------------------------------------------
