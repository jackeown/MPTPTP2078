%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  94 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 356 expanded)
%              Number of equality atoms :   27 (  75 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f38,f48,f55])).

fof(f55,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f53,f33])).

fof(f33,plain,
    ( sK1 != k1_funct_1(sK2,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl6_2
  <=> sK1 = k1_funct_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f53,plain,
    ( sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f52,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f52,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f51,f36])).

fof(f36,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f10,f26])).

fof(f26,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f10,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f50,f13])).

fof(f13,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f30,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f30,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl6_1
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f48,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f46,f12])).

fof(f46,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f45,f36])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f44,f13])).

fof(f44,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f43,f29])).

fof(f29,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f43,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_2 ),
    inference(superposition,[],[f22,f34])).

fof(f34,plain,
    ( sK1 = k1_funct_1(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f37,f32,f28])).

fof(f37,plain,
    ( sK1 != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f9,f36])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | sK1 != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f11,f32,f28])).

fof(f11,plain,
    ( sK1 = k1_funct_1(sK2,sK0)
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:44:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (8347)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (8342)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (8340)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (8354)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (8341)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (8348)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (8341)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f35,f38,f48,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~spl6_1 | spl6_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    $false | (~spl6_1 | spl6_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f53,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    sK1 != k1_funct_1(sK2,sK0) | spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    spl6_2 <=> sK1 = k1_funct_1(sK2,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    sK1 = k1_funct_1(sK2,sK0) | ~spl6_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f52,f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    v1_relat_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f5])).
% 0.22/0.49  fof(f5,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <~> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f3])).
% 0.22/0.49  fof(f3,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | sK1 = k1_funct_1(sK2,sK0) | ~spl6_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f51,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.49    inference(subsumption_resolution,[],[f10,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    r2_hidden(sK0,k1_relat_1(sK2)) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | sK1 = k1_funct_1(sK2,sK0) | ~spl6_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f50,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | sK1 = k1_funct_1(sK2,sK0) | ~spl6_1),
% 0.22/0.49    inference(resolution,[],[f30,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_funct_1(X0,X1) = X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    spl6_1 <=> r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl6_1 | ~spl6_2),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    $false | (spl6_1 | ~spl6_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f46,f12])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | (spl6_1 | ~spl6_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f45,f36])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (spl6_1 | ~spl6_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f44,f13])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (spl6_1 | ~spl6_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f43,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | spl6_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f28])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl6_2),
% 0.22/0.49    inference(superposition,[],[f22,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    sK1 = k1_funct_1(sK2,sK0) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f32])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ~spl6_1 | ~spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f32,f28])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    sK1 != k1_funct_1(sK2,sK0) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f9,f36])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k1_relat_1(sK2)) | sK1 != k1_funct_1(sK2,sK0) | ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    spl6_1 | spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f11,f32,f28])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    sK1 = k1_funct_1(sK2,sK0) | r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (8341)------------------------------
% 0.22/0.49  % (8341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8341)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (8341)Memory used [KB]: 10618
% 0.22/0.49  % (8341)Time elapsed: 0.068 s
% 0.22/0.49  % (8341)------------------------------
% 0.22/0.49  % (8341)------------------------------
% 0.22/0.49  % (8339)Success in time 0.131 s
%------------------------------------------------------------------------------
