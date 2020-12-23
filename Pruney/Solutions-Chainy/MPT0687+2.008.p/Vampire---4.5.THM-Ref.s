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
% DateTime   : Thu Dec  3 12:53:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  82 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 270 expanded)
%              Number of equality atoms :   40 (  92 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f53,f63,f75])).

fof(f75,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f73,f46])).

fof(f46,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl4_2 ),
    inference(superposition,[],[f39,f69])).

fof(f69,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f67,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f67,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f66,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
      | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
    & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
      | r2_hidden(sK0,k2_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | r2_hidden(X0,k2_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
        | ~ r2_hidden(sK0,k2_relat_1(sK1)) )
      & ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
        | r2_hidden(sK0,k2_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,k2_relat_1(X1)) )
      & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
        | r2_hidden(X0,k2_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f66,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f31,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k10_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k10_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f63,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f61,f25])).

fof(f61,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f59,f50])).

fof(f50,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f59,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | spl4_1 ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k10_relat_1(X1,X0) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,
    ( k2_relat_1(sK1) != k2_relat_1(sK1)
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl4_1 ),
    inference(superposition,[],[f34,f54])).

fof(f54,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl4_1 ),
    inference(resolution,[],[f47,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f49,f45])).

fof(f26,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f27,f49,f45])).

fof(f27,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:10:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (6172)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.43  % (6172)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.44  % (6180)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f52,f53,f63,f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ~spl4_1 | ~spl4_2),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    $false | (~spl4_1 | ~spl4_2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f73,f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    spl4_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_2),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    k2_relat_1(sK1) != k2_relat_1(sK1) | ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl4_2),
% 0.21/0.44    inference(superposition,[],[f39,f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl4_2),
% 0.21/0.44    inference(resolution,[],[f67,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl4_2),
% 0.21/0.44    inference(subsumption_resolution,[],[f66,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    (k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))) & (k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) | ~r2_hidden(X0,k2_relat_1(X1))) & (k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) | r2_hidden(X0,k2_relat_1(X1)))) & v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.44    inference(negated_conjecture,[],[f6])).
% 0.21/0.44  fof(f6,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl4_2),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f65])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl4_2),
% 0.21/0.44    inference(superposition,[],[f31,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~spl4_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl4_2 <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1] : (((k10_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl4_1 | spl4_2),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    $false | (spl4_1 | spl4_2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f61,f25])).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    ~v1_relat_1(sK1) | (spl4_1 | spl4_2)),
% 0.21/0.44    inference(subsumption_resolution,[],[f59,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | spl4_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f49])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~v1_relat_1(sK1) | spl4_1),
% 0.21/0.44    inference(resolution,[],[f57,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | k10_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl4_1),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    k2_relat_1(sK1) != k2_relat_1(sK1) | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl4_1),
% 0.21/0.44    inference(superposition,[],[f34,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl4_1),
% 0.21/0.44    inference(resolution,[],[f47,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl4_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f45])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl4_1 | ~spl4_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f26,f49,f45])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ~spl4_1 | spl4_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f27,f49,f45])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (6172)------------------------------
% 0.21/0.44  % (6172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (6172)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (6172)Memory used [KB]: 10618
% 0.21/0.44  % (6172)Time elapsed: 0.059 s
% 0.21/0.44  % (6172)------------------------------
% 0.21/0.44  % (6172)------------------------------
% 0.21/0.45  % (6168)Success in time 0.094 s
%------------------------------------------------------------------------------
