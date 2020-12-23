%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  54 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 133 expanded)
%              Number of equality atoms :   14 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f58,f62])).

fof(f62,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f60,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK0
    | spl6_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f60,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_3 ),
    inference(resolution,[],[f57,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f57,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl6_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f58,plain,
    ( spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f51,f33,f55])).

fof(f33,plain,
    ( spl6_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f51,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f50,f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f50,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f48,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f15,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f15,plain,(
    ! [X2,X1] : ~ r2_hidden(k4_tarski(X1,X2),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
         => k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(f48,plain,
    ( ! [X3] : r1_tarski(sK0,X3)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f43,f15])).

fof(f43,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(sK1(sK0,X3),sK2(sK0,X3)),sK0)
        | r1_tarski(sK0,X3) )
    | ~ spl6_1 ),
    inference(resolution,[],[f35,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f35,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f41,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f14,f33])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (28307)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (28314)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  % (28307)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f36,f41,f58,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl6_2 | ~spl6_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    $false | (spl6_2 | ~spl6_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f60,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    spl6_2 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~spl6_3),
% 0.20/0.48    inference(resolution,[],[f57,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    v1_xboole_0(sK0) | ~spl6_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl6_3 <=> v1_xboole_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl6_3 | ~spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f51,f33,f55])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    spl6_1 <=> v1_relat_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    v1_xboole_0(sK0) | ~spl6_1),
% 0.20/0.48    inference(resolution,[],[f50,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_1),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK0)) ) | ~spl6_1),
% 0.20/0.48    inference(resolution,[],[f48,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_zfmisc_1(X0,X1)) | ~r2_hidden(X2,X3) | ~r2_hidden(X2,sK0)) )),
% 0.20/0.48    inference(superposition,[],[f15,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r2_hidden(k4_tarski(X1,X2),sK0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0] : (k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) & v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0] : ((k1_xboole_0 != X0 & ! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0)) & v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.48    inference(negated_conjecture,[],[f7])).
% 0.20/0.48  fof(f7,conjecture,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X3] : (r1_tarski(sK0,X3)) ) | ~spl6_1),
% 0.20/0.48    inference(subsumption_resolution,[],[f43,f15])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X3] : (r2_hidden(k4_tarski(sK1(sK0,X3),sK2(sK0,X3)),sK0) | r1_tarski(sK0,X3)) ) | ~spl6_1),
% 0.20/0.48    inference(resolution,[],[f35,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_relat_1(sK0) | ~spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f33])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ~spl6_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f38])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f14,f33])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    v1_relat_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (28307)------------------------------
% 0.20/0.48  % (28307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28307)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (28307)Memory used [KB]: 10618
% 0.20/0.48  % (28307)Time elapsed: 0.063 s
% 0.20/0.48  % (28307)------------------------------
% 0.20/0.48  % (28307)------------------------------
% 0.20/0.48  % (28303)Success in time 0.121 s
%------------------------------------------------------------------------------
