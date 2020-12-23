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
% DateTime   : Thu Dec  3 13:08:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 146 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  242 ( 532 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f57,f85,f92])).

fof(f92,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f90,f50])).

fof(f50,plain,
    ( sP0(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_1
  <=> sP0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f90,plain,
    ( ~ sP0(sK2)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f89,f55])).

fof(f55,plain,
    ( ~ v1_finset_1(k3_tarski(sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_2
  <=> v1_finset_1(k3_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f89,plain,
    ( v1_finset_1(k3_tarski(sK2))
    | ~ sP0(sK2)
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f88,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_finset_1(sK3(X0))
      | v1_finset_1(k3_tarski(X0))
      | ~ sP0(X0) ) ),
    inference(subsumption_resolution,[],[f64,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ v1_finset_1(sK1(X0))
          & r2_hidden(sK1(X0),X0) )
        | ~ v1_finset_1(X0) )
      & ( ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK1(X0))
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f64,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(X0)
      | v1_finset_1(sK3(X0))
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f39,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | v1_finset_1(X2)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK3(X0))
        & r2_hidden(sK3(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK3(X0))
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(f88,plain,
    ( ~ v1_finset_1(sK3(sK2))
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f87,f86])).

fof(f86,plain,
    ( v1_finset_1(sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f50,f31])).

fof(f87,plain,
    ( ~ v1_finset_1(sK3(sK2))
    | ~ v1_finset_1(sK2)
    | spl4_2 ),
    inference(resolution,[],[f55,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(sK3(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f83,f61])).

fof(f61,plain,
    ( v1_finset_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,
    ( v1_finset_1(k3_tarski(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_finset_1(k3_tarski(X0))
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f59,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(f59,plain,(
    ! [X1] :
      ( ~ v1_finset_1(k1_zfmisc_1(k3_tarski(X1)))
      | v1_finset_1(X1) ) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

fof(f83,plain,
    ( ~ v1_finset_1(sK2)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f82,f51])).

fof(f51,plain,
    ( ~ sP0(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f82,plain,
    ( sP0(sK2)
    | ~ v1_finset_1(sK2)
    | spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f78,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_finset_1(sK1(X0))
      | sP0(X0)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,
    ( v1_finset_1(sK1(sK2))
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f77,f61])).

fof(f77,plain,
    ( v1_finset_1(sK1(sK2))
    | ~ v1_finset_1(sK2)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f75,f51])).

fof(f75,plain,
    ( v1_finset_1(sK1(sK2))
    | sP0(sK2)
    | ~ v1_finset_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f73,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | sP0(X0)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v1_finset_1(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f71,f54])).

fof(f71,plain,(
    ! [X2,X3] :
      ( ~ v1_finset_1(k3_tarski(X3))
      | ~ r2_hidden(X2,X3)
      | v1_finset_1(X2) ) ),
    inference(resolution,[],[f68,f41])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f45,f46])).

fof(f46,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

% (12577)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f57,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f35,f53,f49])).

fof(f35,plain,
    ( v1_finset_1(k3_tarski(sK2))
    | sP0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK2))
      | ~ sP0(sK2) )
    & ( v1_finset_1(k3_tarski(sK2))
      | sP0(sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ~ sP0(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | sP0(X0) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK2))
        | ~ sP0(sK2) )
      & ( v1_finset_1(k3_tarski(sK2))
        | sP0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ~ sP0(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( sP0(X0)
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(definition_folding,[],[f9,f17])).

fof(f9,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(f56,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f53,f49])).

fof(f36,plain,
    ( ~ v1_finset_1(k3_tarski(sK2))
    | ~ sP0(sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:46:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (12595)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (12575)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (12576)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (12575)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f56,f57,f85,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ~spl4_1 | spl4_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    $false | (~spl4_1 | spl4_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f90,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    sP0(sK2) | ~spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    spl4_1 <=> sP0(sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ~sP0(sK2) | (~spl4_1 | spl4_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f89,f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~v1_finset_1(k3_tarski(sK2)) | spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    spl4_2 <=> v1_finset_1(k3_tarski(sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    v1_finset_1(k3_tarski(sK2)) | ~sP0(sK2) | (~spl4_1 | spl4_2)),
% 0.22/0.52    inference(resolution,[],[f88,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0] : (v1_finset_1(sK3(X0)) | v1_finset_1(k3_tarski(X0)) | ~sP0(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f64,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (~sP0(X0) | v1_finset_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : ((sP0(X0) | (~v1_finset_1(sK1(X0)) & r2_hidden(sK1(X0),X0)) | ~v1_finset_1(X0)) & ((! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0)) | ~sP0(X0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) => (~v1_finset_1(sK1(X0)) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : ((sP0(X0) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & ((! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0)) | ~sP0(X0)))),
% 0.22/0.52    inference(rectify,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : ((sP0(X0) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) | ~sP0(X0)))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : ((sP0(X0) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))) & ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) | ~sP0(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (sP0(X0) <=> (! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0] : (v1_finset_1(k3_tarski(X0)) | ~v1_finset_1(X0) | v1_finset_1(sK3(X0)) | ~sP0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f39,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | v1_finset_1(X2) | ~sP0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_finset_1(k3_tarski(X0)) | ~v1_finset_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (~v1_finset_1(sK3(X0)) & r2_hidden(sK3(X0),X0)) | ~v1_finset_1(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) => (~v1_finset_1(sK3(X0)) & r2_hidden(sK3(X0),X0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) => v1_finset_1(k3_tarski(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ~v1_finset_1(sK3(sK2)) | (~spl4_1 | spl4_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f87,f86])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    v1_finset_1(sK2) | ~spl4_1),
% 0.22/0.52    inference(resolution,[],[f50,f31])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ~v1_finset_1(sK3(sK2)) | ~v1_finset_1(sK2) | spl4_2),
% 0.22/0.52    inference(resolution,[],[f55,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0] : (v1_finset_1(k3_tarski(X0)) | ~v1_finset_1(sK3(X0)) | ~v1_finset_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    spl4_1 | ~spl4_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    $false | (spl4_1 | ~spl4_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f83,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    v1_finset_1(sK2) | ~spl4_2),
% 0.22/0.52    inference(resolution,[],[f60,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    v1_finset_1(k3_tarski(sK2)) | ~spl4_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f53])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_finset_1(k3_tarski(X0)) | v1_finset_1(X0)) )),
% 0.22/0.52    inference(resolution,[],[f59,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (v1_finset_1(X0) => v1_finset_1(k1_zfmisc_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X1] : (~v1_finset_1(k1_zfmisc_1(k3_tarski(X1))) | v1_finset_1(X1)) )),
% 0.22/0.52    inference(resolution,[],[f41,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ~v1_finset_1(sK2) | (spl4_1 | ~spl4_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f82,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ~sP0(sK2) | spl4_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f49])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    sP0(sK2) | ~v1_finset_1(sK2) | (spl4_1 | ~spl4_2)),
% 0.22/0.52    inference(resolution,[],[f78,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_finset_1(sK1(X0)) | sP0(X0) | ~v1_finset_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    v1_finset_1(sK1(sK2)) | (spl4_1 | ~spl4_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f77,f61])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    v1_finset_1(sK1(sK2)) | ~v1_finset_1(sK2) | (spl4_1 | ~spl4_2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f75,f51])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    v1_finset_1(sK1(sK2)) | sP0(sK2) | ~v1_finset_1(sK2) | ~spl4_2),
% 0.22/0.52    inference(resolution,[],[f73,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK1(X0),X0) | sP0(X0) | ~v1_finset_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | v1_finset_1(X0)) ) | ~spl4_2),
% 0.22/0.52    inference(resolution,[],[f71,f54])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~v1_finset_1(k3_tarski(X3)) | ~r2_hidden(X2,X3) | v1_finset_1(X2)) )),
% 0.22/0.52    inference(resolution,[],[f68,f41])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f45,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.22/0.52  % (12577)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl4_1 | spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f35,f53,f49])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    v1_finset_1(k3_tarski(sK2)) | sP0(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    (~v1_finset_1(k3_tarski(sK2)) | ~sP0(sK2)) & (v1_finset_1(k3_tarski(sK2)) | sP0(sK2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ~sP0(X0)) & (v1_finset_1(k3_tarski(X0)) | sP0(X0))) => ((~v1_finset_1(k3_tarski(sK2)) | ~sP0(sK2)) & (v1_finset_1(k3_tarski(sK2)) | sP0(sK2)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ~sP0(X0)) & (v1_finset_1(k3_tarski(X0)) | sP0(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0] : (sP0(X0) <~> v1_finset_1(k3_tarski(X0)))),
% 0.22/0.52    inference(definition_folding,[],[f9,f17])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0] : ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) <~> v1_finset_1(k3_tarski(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.22/0.52    inference(negated_conjecture,[],[f7])).
% 0.22/0.52  fof(f7,conjecture,(
% 0.22/0.52    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ~spl4_1 | ~spl4_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f36,f53,f49])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ~v1_finset_1(k3_tarski(sK2)) | ~sP0(sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (12575)------------------------------
% 0.22/0.52  % (12575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12575)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (12575)Memory used [KB]: 6140
% 0.22/0.52  % (12575)Time elapsed: 0.099 s
% 0.22/0.52  % (12575)------------------------------
% 0.22/0.52  % (12575)------------------------------
% 0.22/0.52  % (12570)Success in time 0.155 s
%------------------------------------------------------------------------------
