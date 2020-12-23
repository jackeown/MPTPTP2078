%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:20 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 214 expanded)
%              Number of leaves         :   11 (  59 expanded)
%              Depth                    :   21
%              Number of atoms          :  243 ( 889 expanded)
%              Number of equality atoms :   21 (  76 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f54])).

fof(f54,plain,(
    v1_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) )
     => v1_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f52,plain,
    ( v1_ordinal1(sK1)
    | r1_tarski(sK2(sK1),sK1) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r1_tarski(X1,sK1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v3_ordinal1(sK1)
    & ! [X1] :
        ( ( r1_tarski(X1,sK1)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(X0)
        & ! [X1] :
            ( ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) )
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(sK1)
      & ! [X1] :
          ( ( r1_tarski(X1,sK1)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    ~ v1_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f94,f34])).

fof(f34,plain,(
    ~ v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,
    ( v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK1) ),
    inference(resolution,[],[f93,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(f93,plain,(
    v2_ordinal1(sK1) ),
    inference(resolution,[],[f92,f44])).

fof(f44,plain,(
    ! [X0] :
      ( sP0(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | sP0(X0) ) ),
    inference(definition_folding,[],[f17,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f17,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) )
     => v2_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f92,plain,(
    ~ sP0(sK1) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( sK3(sK1) != sK3(sK1)
    | ~ sP0(sK1) ),
    inference(superposition,[],[f42,f79])).

fof(f79,plain,(
    sK3(sK1) = sK4(sK1) ),
    inference(subsumption_resolution,[],[f78,f54])).

fof(f78,plain,
    ( sK3(sK1) = sK4(sK1)
    | ~ v1_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f77,f34])).

fof(f77,plain,
    ( sK3(sK1) = sK4(sK1)
    | v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK1) ),
    inference(resolution,[],[f75,f36])).

fof(f75,plain,
    ( v2_ordinal1(sK1)
    | sK3(sK1) = sK4(sK1) ),
    inference(subsumption_resolution,[],[f71,f74])).

fof(f74,plain,
    ( r1_tarski(sK4(sK1),sK3(sK1))
    | v2_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f73,f44])).

fof(f73,plain,
    ( r1_tarski(sK4(sK1),sK3(sK1))
    | v2_ordinal1(sK1)
    | ~ sP0(sK1) ),
    inference(subsumption_resolution,[],[f72,f58])).

fof(f58,plain,
    ( v3_ordinal1(sK3(sK1))
    | v2_ordinal1(sK1) ),
    inference(resolution,[],[f55,f32])).

fof(f32,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(resolution,[],[f39,f44])).

fof(f39,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ~ r2_hidden(sK4(X0),sK3(X0))
        & sK3(X0) != sK4(X0)
        & ~ r2_hidden(sK3(X0),sK4(X0))
        & r2_hidden(sK4(X0),X0)
        & r2_hidden(sK3(X0),X0) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK4(X0),sK3(X0))
        & sK3(X0) != sK4(X0)
        & ~ r2_hidden(sK3(X0),sK4(X0))
        & r2_hidden(sK4(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f72,plain,
    ( r1_tarski(sK4(sK1),sK3(sK1))
    | ~ v3_ordinal1(sK3(sK1))
    | v2_ordinal1(sK1)
    | ~ sP0(sK1) ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK4(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK4(sK1))
      | r1_tarski(sK4(sK1),X1)
      | ~ v3_ordinal1(X1)
      | v2_ordinal1(sK1) ) ),
    inference(resolution,[],[f65,f60])).

fof(f60,plain,
    ( v3_ordinal1(sK4(sK1))
    | v2_ordinal1(sK1) ),
    inference(resolution,[],[f56,f32])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(resolution,[],[f40,f44])).

fof(f40,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f71,plain,
    ( v2_ordinal1(sK1)
    | ~ r1_tarski(sK4(sK1),sK3(sK1))
    | sK3(sK1) = sK4(sK1) ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70,plain,
    ( r1_tarski(sK3(sK1),sK4(sK1))
    | v2_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f69,f44])).

fof(f69,plain,
    ( r1_tarski(sK3(sK1),sK4(sK1))
    | v2_ordinal1(sK1)
    | ~ sP0(sK1) ),
    inference(subsumption_resolution,[],[f68,f60])).

fof(f68,plain,
    ( r1_tarski(sK3(sK1),sK4(sK1))
    | ~ v3_ordinal1(sK4(sK1))
    | v2_ordinal1(sK1)
    | ~ sP0(sK1) ),
    inference(resolution,[],[f66,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0),sK3(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK3(sK1))
      | r1_tarski(sK3(sK1),X0)
      | ~ v3_ordinal1(X0)
      | v2_ordinal1(sK1) ) ),
    inference(resolution,[],[f65,f58])).

fof(f42,plain,(
    ! [X0] :
      ( sK3(X0) != sK4(X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (29629)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (29620)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (29627)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (29643)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.24/0.51  % (29637)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.24/0.51  % (29619)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.24/0.52  % (29619)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % SZS output start Proof for theBenchmark
% 1.24/0.52  fof(f96,plain,(
% 1.24/0.52    $false),
% 1.24/0.52    inference(subsumption_resolution,[],[f95,f54])).
% 1.24/0.52  fof(f54,plain,(
% 1.24/0.52    v1_ordinal1(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f52,f38])).
% 1.24/0.52  fof(f38,plain,(
% 1.24/0.52    ( ! [X0] : (~r1_tarski(sK2(X0),X0) | v1_ordinal1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  fof(f25,plain,(
% 1.24/0.52    ! [X0] : (v1_ordinal1(X0) | (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f24])).
% 1.24/0.52  fof(f24,plain,(
% 1.24/0.52    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f16,plain,(
% 1.24/0.52    ! [X0] : (v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f10])).
% 1.24/0.52  fof(f10,plain,(
% 1.24/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)) => v1_ordinal1(X0))),
% 1.24/0.52    inference(unused_predicate_definition_removal,[],[f3])).
% 1.24/0.52  fof(f3,axiom,(
% 1.24/0.52    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 1.24/0.52  fof(f52,plain,(
% 1.24/0.52    v1_ordinal1(sK1) | r1_tarski(sK2(sK1),sK1)),
% 1.24/0.52    inference(resolution,[],[f37,f33])).
% 1.24/0.52  fof(f33,plain,(
% 1.24/0.52    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(X1,sK1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f23])).
% 1.24/0.52  fof(f23,plain,(
% 1.24/0.52    ~v3_ordinal1(sK1) & ! [X1] : ((r1_tarski(X1,sK1) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK1))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f22])).
% 1.24/0.52  fof(f22,plain,(
% 1.24/0.52    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0))) => (~v3_ordinal1(sK1) & ! [X1] : ((r1_tarski(X1,sK1) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK1)))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f11,plain,(
% 1.24/0.52    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f8])).
% 1.24/0.52  fof(f8,negated_conjecture,(
% 1.24/0.52    ~! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 1.24/0.52    inference(negated_conjecture,[],[f7])).
% 1.24/0.52  fof(f7,conjecture,(
% 1.24/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_ordinal1)).
% 1.24/0.52  fof(f37,plain,(
% 1.24/0.52    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_ordinal1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f25])).
% 1.24/0.52  fof(f95,plain,(
% 1.24/0.52    ~v1_ordinal1(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f94,f34])).
% 1.24/0.52  fof(f34,plain,(
% 1.24/0.52    ~v3_ordinal1(sK1)),
% 1.24/0.52    inference(cnf_transformation,[],[f23])).
% 1.24/0.52  fof(f94,plain,(
% 1.24/0.52    v3_ordinal1(sK1) | ~v1_ordinal1(sK1)),
% 1.24/0.52    inference(resolution,[],[f93,f36])).
% 1.24/0.52  fof(f36,plain,(
% 1.24/0.52    ( ! [X0] : (~v2_ordinal1(X0) | v3_ordinal1(X0) | ~v1_ordinal1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f15])).
% 1.24/0.52  fof(f15,plain,(
% 1.24/0.52    ! [X0] : (v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0))),
% 1.24/0.52    inference(flattening,[],[f14])).
% 1.24/0.52  fof(f14,plain,(
% 1.24/0.52    ! [X0] : (v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f2])).
% 1.24/0.52  fof(f2,axiom,(
% 1.24/0.52    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) => v3_ordinal1(X0))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_ordinal1)).
% 1.24/0.52  fof(f93,plain,(
% 1.24/0.52    v2_ordinal1(sK1)),
% 1.24/0.52    inference(resolution,[],[f92,f44])).
% 1.24/0.52  fof(f44,plain,(
% 1.24/0.52    ( ! [X0] : (sP0(X0) | v2_ordinal1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f21])).
% 1.24/0.52  fof(f21,plain,(
% 1.24/0.52    ! [X0] : (v2_ordinal1(X0) | sP0(X0))),
% 1.24/0.52    inference(definition_folding,[],[f17,f20])).
% 1.24/0.52  fof(f20,plain,(
% 1.24/0.52    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) | ~sP0(X0))),
% 1.24/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.24/0.52  fof(f17,plain,(
% 1.24/0.52    ! [X0] : (v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f9])).
% 1.24/0.52  fof(f9,plain,(
% 1.24/0.52    ! [X0] : (! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => v2_ordinal1(X0))),
% 1.24/0.52    inference(unused_predicate_definition_removal,[],[f4])).
% 1.24/0.52  fof(f4,axiom,(
% 1.24/0.52    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_ordinal1)).
% 1.24/0.52  fof(f92,plain,(
% 1.24/0.52    ~sP0(sK1)),
% 1.24/0.52    inference(trivial_inequality_removal,[],[f89])).
% 1.24/0.52  fof(f89,plain,(
% 1.24/0.52    sK3(sK1) != sK3(sK1) | ~sP0(sK1)),
% 1.24/0.52    inference(superposition,[],[f42,f79])).
% 1.24/0.52  fof(f79,plain,(
% 1.24/0.52    sK3(sK1) = sK4(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f78,f54])).
% 1.24/0.52  fof(f78,plain,(
% 1.24/0.52    sK3(sK1) = sK4(sK1) | ~v1_ordinal1(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f77,f34])).
% 1.24/0.52  fof(f77,plain,(
% 1.24/0.52    sK3(sK1) = sK4(sK1) | v3_ordinal1(sK1) | ~v1_ordinal1(sK1)),
% 1.24/0.52    inference(resolution,[],[f75,f36])).
% 1.24/0.52  fof(f75,plain,(
% 1.24/0.52    v2_ordinal1(sK1) | sK3(sK1) = sK4(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f71,f74])).
% 1.24/0.52  fof(f74,plain,(
% 1.24/0.52    r1_tarski(sK4(sK1),sK3(sK1)) | v2_ordinal1(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f73,f44])).
% 1.24/0.52  fof(f73,plain,(
% 1.24/0.52    r1_tarski(sK4(sK1),sK3(sK1)) | v2_ordinal1(sK1) | ~sP0(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f72,f58])).
% 1.24/0.52  fof(f58,plain,(
% 1.24/0.52    v3_ordinal1(sK3(sK1)) | v2_ordinal1(sK1)),
% 1.24/0.52    inference(resolution,[],[f55,f32])).
% 1.24/0.52  fof(f32,plain,(
% 1.24/0.52    ( ! [X1] : (~r2_hidden(X1,sK1) | v3_ordinal1(X1)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f23])).
% 1.24/0.52  fof(f55,plain,(
% 1.24/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v2_ordinal1(X0)) )),
% 1.24/0.52    inference(resolution,[],[f39,f44])).
% 1.24/0.52  fof(f39,plain,(
% 1.24/0.52    ( ! [X0] : (~sP0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  fof(f28,plain,(
% 1.24/0.52    ! [X0] : ((~r2_hidden(sK4(X0),sK3(X0)) & sK3(X0) != sK4(X0) & ~r2_hidden(sK3(X0),sK4(X0)) & r2_hidden(sK4(X0),X0) & r2_hidden(sK3(X0),X0)) | ~sP0(X0))),
% 1.24/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f26,f27])).
% 1.24/0.52  fof(f27,plain,(
% 1.24/0.52    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(sK4(X0),sK3(X0)) & sK3(X0) != sK4(X0) & ~r2_hidden(sK3(X0),sK4(X0)) & r2_hidden(sK4(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 1.24/0.52    introduced(choice_axiom,[])).
% 1.24/0.52  fof(f26,plain,(
% 1.24/0.52    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) | ~sP0(X0))),
% 1.24/0.52    inference(nnf_transformation,[],[f20])).
% 1.24/0.52  fof(f72,plain,(
% 1.24/0.52    r1_tarski(sK4(sK1),sK3(sK1)) | ~v3_ordinal1(sK3(sK1)) | v2_ordinal1(sK1) | ~sP0(sK1)),
% 1.24/0.52    inference(resolution,[],[f67,f41])).
% 1.24/0.52  fof(f41,plain,(
% 1.24/0.52    ( ! [X0] : (~r2_hidden(sK3(X0),sK4(X0)) | ~sP0(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  fof(f67,plain,(
% 1.24/0.52    ( ! [X1] : (r2_hidden(X1,sK4(sK1)) | r1_tarski(sK4(sK1),X1) | ~v3_ordinal1(X1) | v2_ordinal1(sK1)) )),
% 1.24/0.52    inference(resolution,[],[f65,f60])).
% 1.24/0.52  fof(f60,plain,(
% 1.24/0.52    v3_ordinal1(sK4(sK1)) | v2_ordinal1(sK1)),
% 1.24/0.52    inference(resolution,[],[f56,f32])).
% 1.24/0.52  fof(f56,plain,(
% 1.24/0.52    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v2_ordinal1(X0)) )),
% 1.24/0.52    inference(resolution,[],[f40,f44])).
% 1.24/0.52  fof(f40,plain,(
% 1.24/0.52    ( ! [X0] : (~sP0(X0) | r2_hidden(sK4(X0),X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  fof(f65,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | r2_hidden(X1,X0)) )),
% 1.24/0.52    inference(duplicate_literal_removal,[],[f64])).
% 1.24/0.52  fof(f64,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.24/0.52    inference(resolution,[],[f45,f35])).
% 1.24/0.52  fof(f35,plain,(
% 1.24/0.52    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f13])).
% 1.24/0.52  fof(f13,plain,(
% 1.24/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.24/0.52    inference(flattening,[],[f12])).
% 1.24/0.52  fof(f12,plain,(
% 1.24/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.24/0.52    inference(ennf_transformation,[],[f6])).
% 1.24/0.52  fof(f6,axiom,(
% 1.24/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.24/0.52  fof(f45,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f29])).
% 1.24/0.52  fof(f29,plain,(
% 1.24/0.52    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.24/0.52    inference(nnf_transformation,[],[f19])).
% 1.24/0.52  fof(f19,plain,(
% 1.24/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.24/0.52    inference(flattening,[],[f18])).
% 1.24/0.52  fof(f18,plain,(
% 1.24/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.24/0.52    inference(ennf_transformation,[],[f5])).
% 1.24/0.52  fof(f5,axiom,(
% 1.24/0.52    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.24/0.52  fof(f71,plain,(
% 1.24/0.52    v2_ordinal1(sK1) | ~r1_tarski(sK4(sK1),sK3(sK1)) | sK3(sK1) = sK4(sK1)),
% 1.24/0.52    inference(resolution,[],[f70,f49])).
% 1.24/0.52  fof(f49,plain,(
% 1.24/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.24/0.52    inference(cnf_transformation,[],[f31])).
% 1.24/0.52  fof(f31,plain,(
% 1.24/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.52    inference(flattening,[],[f30])).
% 1.24/0.52  fof(f30,plain,(
% 1.24/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.24/0.52    inference(nnf_transformation,[],[f1])).
% 1.24/0.52  fof(f1,axiom,(
% 1.24/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.52  fof(f70,plain,(
% 1.24/0.52    r1_tarski(sK3(sK1),sK4(sK1)) | v2_ordinal1(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f69,f44])).
% 1.24/0.52  fof(f69,plain,(
% 1.24/0.52    r1_tarski(sK3(sK1),sK4(sK1)) | v2_ordinal1(sK1) | ~sP0(sK1)),
% 1.24/0.52    inference(subsumption_resolution,[],[f68,f60])).
% 1.24/0.52  fof(f68,plain,(
% 1.24/0.52    r1_tarski(sK3(sK1),sK4(sK1)) | ~v3_ordinal1(sK4(sK1)) | v2_ordinal1(sK1) | ~sP0(sK1)),
% 1.24/0.52    inference(resolution,[],[f66,f43])).
% 1.24/0.52  fof(f43,plain,(
% 1.24/0.52    ( ! [X0] : (~r2_hidden(sK4(X0),sK3(X0)) | ~sP0(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  fof(f66,plain,(
% 1.24/0.52    ( ! [X0] : (r2_hidden(X0,sK3(sK1)) | r1_tarski(sK3(sK1),X0) | ~v3_ordinal1(X0) | v2_ordinal1(sK1)) )),
% 1.24/0.52    inference(resolution,[],[f65,f58])).
% 1.24/0.52  fof(f42,plain,(
% 1.24/0.52    ( ! [X0] : (sK3(X0) != sK4(X0) | ~sP0(X0)) )),
% 1.24/0.52    inference(cnf_transformation,[],[f28])).
% 1.24/0.52  % SZS output end Proof for theBenchmark
% 1.24/0.52  % (29619)------------------------------
% 1.24/0.52  % (29619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (29619)Termination reason: Refutation
% 1.24/0.52  
% 1.24/0.52  % (29619)Memory used [KB]: 6140
% 1.24/0.52  % (29619)Time elapsed: 0.100 s
% 1.24/0.52  % (29619)------------------------------
% 1.24/0.52  % (29619)------------------------------
% 1.24/0.52  % (29629)Refutation not found, incomplete strategy% (29629)------------------------------
% 1.24/0.52  % (29629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (29629)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (29629)Memory used [KB]: 6012
% 1.24/0.52  % (29629)Time elapsed: 0.103 s
% 1.24/0.52  % (29629)------------------------------
% 1.24/0.52  % (29629)------------------------------
% 1.24/0.52  % (29623)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.24/0.52  % (29607)Success in time 0.16 s
%------------------------------------------------------------------------------
