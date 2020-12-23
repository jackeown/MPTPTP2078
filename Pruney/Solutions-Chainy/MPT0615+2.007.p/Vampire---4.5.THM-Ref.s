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
% DateTime   : Thu Dec  3 12:51:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  90 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  170 ( 391 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f43,f87,f105])).

fof(f105,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f103,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
      | ~ r1_tarski(sK0,sK1) )
    & ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
      | r1_tarski(sK0,sK1) )
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | ~ r1_tarski(X0,X1) )
            & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | r1_tarski(X0,X1) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
            | ~ r1_tarski(sK0,X1) )
          & ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
            | r1_tarski(sK0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
          | ~ r1_tarski(sK0,X1) )
        & ( r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0)))
          | r1_tarski(sK0,X1) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
        | ~ r1_tarski(sK0,sK1) )
      & ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
        | r1_tarski(sK0,sK1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | ~ r1_tarski(X0,X1) )
          & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
            | r1_tarski(X0,X1) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

fof(f103,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f102,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f101,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f101,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f99,f36])).

fof(f36,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f99,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | spl2_2 ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

fof(f41,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f87,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f86])).

fof(f86,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f84,f22])).

fof(f84,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f74,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f74,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f71,f40])).

fof(f40,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f71,plain,
    ( ! [X8] :
        ( ~ r1_tarski(sK0,X8)
        | ~ r1_tarski(X8,sK1) )
    | spl2_1 ),
    inference(resolution,[],[f45,f37])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f31,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f43,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f23,f39,f35])).

fof(f23,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f39,f35])).

fof(f24,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (27211)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (27205)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (27205)Refutation not found, incomplete strategy% (27205)------------------------------
% 0.20/0.49  % (27205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (27210)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (27205)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (27205)Memory used [KB]: 10490
% 0.20/0.49  % (27205)Time elapsed: 0.080 s
% 0.20/0.49  % (27205)------------------------------
% 0.20/0.49  % (27205)------------------------------
% 0.20/0.49  % (27210)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f42,f43,f87,f105])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ~spl2_1 | spl2_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    $false | (~spl2_1 | spl2_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f103,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    v1_relat_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) => ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((r1_tarski(X0,X1) <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ~v1_relat_1(sK1) | (~spl2_1 | spl2_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f102,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    v1_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | (~spl2_1 | spl2_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f101,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | (~spl2_1 | spl2_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f99,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl2_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | spl2_2),
% 0.20/0.49    inference(resolution,[],[f41,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X2,k7_relat_1(X1,X0)) | ~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k7_relat_1(X1,X0)) | ~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k7_relat_1(X1,X0)) | (~r1_tarski(X2,X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    spl2_2 <=> r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl2_1 | ~spl2_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    $false | (spl2_1 | ~spl2_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f84,f22])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    ~v1_relat_1(sK1) | (spl2_1 | ~spl2_2)),
% 0.20/0.49    inference(resolution,[],[f74,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ~r1_tarski(k7_relat_1(sK1,k1_relat_1(sK0)),sK1) | (spl2_1 | ~spl2_2)),
% 0.20/0.49    inference(resolution,[],[f71,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f39])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X8] : (~r1_tarski(sK0,X8) | ~r1_tarski(X8,sK1)) ) | spl2_1),
% 0.20/0.49    inference(resolution,[],[f45,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK1) | spl2_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f35])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(superposition,[],[f31,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    spl2_1 | spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f39,f35])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~spl2_1 | ~spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f24,f39,f35])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (27210)------------------------------
% 0.20/0.49  % (27210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (27210)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (27210)Memory used [KB]: 6140
% 0.20/0.49  % (27210)Time elapsed: 0.091 s
% 0.20/0.49  % (27210)------------------------------
% 0.20/0.49  % (27210)------------------------------
% 0.20/0.49  % (27201)Success in time 0.137 s
%------------------------------------------------------------------------------
