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
% DateTime   : Thu Dec  3 12:46:55 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   39 (  62 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 178 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f136])).

fof(f136,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f134,f30])).

fof(f30,plain,
    ( v1_relat_1(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl7_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f134,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f133,f35])).

fof(f35,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl7_2
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f133,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl7_1 ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl7_1 ),
    inference(resolution,[],[f81,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f81,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(sK1(sK0,X6),sK2(sK0,X7)),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
        | r1_tarski(sK0,X7)
        | r1_tarski(sK0,X6) )
    | ~ spl7_1 ),
    inference(resolution,[],[f56,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f56,plain,
    ( ! [X4,X5] :
        ( sP4(k4_tarski(sK1(sK0,X4),sK2(sK0,X5)),k2_relat_1(sK0),k1_relat_1(sK0))
        | r1_tarski(sK0,X4)
        | r1_tarski(sK0,X5) )
    | ~ spl7_1 ),
    inference(resolution,[],[f51,f45])).

fof(f45,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(sK0,X1),k2_relat_1(sK0))
        | r1_tarski(sK0,X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f39,f30])).

fof(f39,plain,
    ( ! [X1] :
        ( r1_tarski(sK0,X1)
        | ~ v1_relat_1(sK0)
        | r2_hidden(sK2(sK0,X1),k2_relat_1(sK0)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f32,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK1(sK0,X0),sK2(sK0,X0)),sK0)
        | r1_tarski(sK0,X0) )
    | ~ spl7_1 ),
    inference(resolution,[],[f30,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,X2)
        | r1_tarski(sK0,X0)
        | sP4(k4_tarski(sK1(sK0,X0),X1),X2,k1_relat_1(sK0)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | sP4(k4_tarski(X4,X5),X1,X0) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f44,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(sK0,X0),k1_relat_1(sK0))
        | r1_tarski(sK0,X0) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f38,f30])).

fof(f38,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,X0)
        | ~ v1_relat_1(sK0)
        | r2_hidden(sK1(sK0,X0),k1_relat_1(sK0)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f32,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f36,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f11,f34])).

fof(f11,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f31,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f10,f29])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:03:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.45  % (14860)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.46  % (14859)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.46  % (14860)Refutation not found, incomplete strategy% (14860)------------------------------
% 0.18/0.46  % (14860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (14860)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  
% 0.18/0.46  % (14860)Memory used [KB]: 10490
% 0.18/0.46  % (14860)Time elapsed: 0.065 s
% 0.18/0.46  % (14860)------------------------------
% 0.18/0.46  % (14860)------------------------------
% 0.18/0.46  % (14863)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.46  % (14878)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.46  % (14867)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.18/0.47  % (14870)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.18/0.47  % (14859)Refutation found. Thanks to Tanya!
% 0.18/0.47  % SZS status Theorem for theBenchmark
% 0.18/0.47  % (14874)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.47  % (14873)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.47  % (14864)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f137,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(avatar_sat_refutation,[],[f31,f36,f136])).
% 0.18/0.48  fof(f136,plain,(
% 0.18/0.48    ~spl7_1 | spl7_2),
% 0.18/0.48    inference(avatar_contradiction_clause,[],[f135])).
% 0.18/0.48  fof(f135,plain,(
% 0.18/0.48    $false | (~spl7_1 | spl7_2)),
% 0.18/0.48    inference(subsumption_resolution,[],[f134,f30])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    v1_relat_1(sK0) | ~spl7_1),
% 0.18/0.48    inference(avatar_component_clause,[],[f29])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    spl7_1 <=> v1_relat_1(sK0)),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.18/0.48  fof(f134,plain,(
% 0.18/0.48    ~v1_relat_1(sK0) | (~spl7_1 | spl7_2)),
% 0.18/0.48    inference(subsumption_resolution,[],[f133,f35])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl7_2),
% 0.18/0.48    inference(avatar_component_clause,[],[f34])).
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    spl7_2 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.18/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.18/0.48  fof(f133,plain,(
% 0.18/0.48    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~v1_relat_1(sK0) | ~spl7_1),
% 0.18/0.48    inference(duplicate_literal_removal,[],[f122])).
% 0.18/0.48  fof(f122,plain,(
% 0.18/0.48    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~v1_relat_1(sK0) | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl7_1),
% 0.18/0.48    inference(resolution,[],[f81,f14])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.18/0.48  fof(f81,plain,(
% 0.18/0.48    ( ! [X6,X7] : (r2_hidden(k4_tarski(sK1(sK0,X6),sK2(sK0,X7)),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | r1_tarski(sK0,X7) | r1_tarski(sK0,X6)) ) | ~spl7_1),
% 0.18/0.48    inference(resolution,[],[f56,f26])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.18/0.48    inference(equality_resolution,[],[f19])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.18/0.48    inference(cnf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.18/0.48  fof(f56,plain,(
% 0.18/0.48    ( ! [X4,X5] : (sP4(k4_tarski(sK1(sK0,X4),sK2(sK0,X5)),k2_relat_1(sK0),k1_relat_1(sK0)) | r1_tarski(sK0,X4) | r1_tarski(sK0,X5)) ) | ~spl7_1),
% 0.18/0.48    inference(resolution,[],[f51,f45])).
% 0.18/0.48  fof(f45,plain,(
% 0.18/0.48    ( ! [X1] : (r2_hidden(sK2(sK0,X1),k2_relat_1(sK0)) | r1_tarski(sK0,X1)) ) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f39,f30])).
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    ( ! [X1] : (r1_tarski(sK0,X1) | ~v1_relat_1(sK0) | r2_hidden(sK2(sK0,X1),k2_relat_1(sK0))) ) | ~spl7_1),
% 0.18/0.48    inference(resolution,[],[f32,f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f9])).
% 0.18/0.48  fof(f9,plain,(
% 0.18/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.18/0.48    inference(flattening,[],[f8])).
% 0.18/0.48  fof(f8,plain,(
% 0.18/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.18/0.48    inference(ennf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    ( ! [X0] : (r2_hidden(k4_tarski(sK1(sK0,X0),sK2(sK0,X0)),sK0) | r1_tarski(sK0,X0)) ) | ~spl7_1),
% 0.18/0.48    inference(resolution,[],[f30,f13])).
% 0.18/0.48  fof(f13,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f7])).
% 0.18/0.48  fof(f51,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | r1_tarski(sK0,X0) | sP4(k4_tarski(sK1(sK0,X0),X1),X2,k1_relat_1(sK0))) ) | ~spl7_1),
% 0.18/0.48    inference(resolution,[],[f44,f27])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | sP4(k4_tarski(X4,X5),X1,X0)) )),
% 0.18/0.48    inference(equality_resolution,[],[f15])).
% 0.18/0.48  fof(f15,plain,(
% 0.18/0.48    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP4(X3,X1,X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f1])).
% 0.18/0.48  fof(f44,plain,(
% 0.18/0.48    ( ! [X0] : (r2_hidden(sK1(sK0,X0),k1_relat_1(sK0)) | r1_tarski(sK0,X0)) ) | ~spl7_1),
% 0.18/0.48    inference(subsumption_resolution,[],[f38,f30])).
% 0.18/0.48  fof(f38,plain,(
% 0.18/0.48    ( ! [X0] : (r1_tarski(sK0,X0) | ~v1_relat_1(sK0) | r2_hidden(sK1(sK0,X0),k1_relat_1(sK0))) ) | ~spl7_1),
% 0.18/0.48    inference(resolution,[],[f32,f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f9])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    ~spl7_2),
% 0.18/0.48    inference(avatar_split_clause,[],[f11,f34])).
% 0.18/0.48  fof(f11,plain,(
% 0.18/0.48    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.18/0.48    inference(cnf_transformation,[],[f6])).
% 0.18/0.48  fof(f6,plain,(
% 0.18/0.48    ? [X0] : (~r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) & v1_relat_1(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f5])).
% 0.18/0.48  fof(f5,negated_conjecture,(
% 0.18/0.48    ~! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.18/0.48    inference(negated_conjecture,[],[f4])).
% 0.18/0.48  fof(f4,conjecture,(
% 0.18/0.48    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.18/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    spl7_1),
% 0.18/0.48    inference(avatar_split_clause,[],[f10,f29])).
% 0.18/0.48  fof(f10,plain,(
% 0.18/0.48    v1_relat_1(sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f6])).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (14859)------------------------------
% 0.18/0.48  % (14859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (14859)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (14859)Memory used [KB]: 6268
% 0.18/0.48  % (14859)Time elapsed: 0.054 s
% 0.18/0.48  % (14859)------------------------------
% 0.18/0.48  % (14859)------------------------------
% 0.18/0.48  % (14879)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.18/0.48  % (14872)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.48  % (14853)Success in time 0.136 s
%------------------------------------------------------------------------------
