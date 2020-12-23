%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  80 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  146 ( 364 expanded)
%              Number of equality atoms :   16 (  60 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f20,f19,f29,f23,f21,f103])).

fof(f103,plain,(
    ! [X2,X3] :
      ( r2_xboole_0(X3,X2)
      | ~ v3_ordinal1(X3)
      | r2_xboole_0(X2,X3)
      | sQ2_eqProxy(X3,X2)
      | ~ v3_ordinal1(X2) ) ),
    inference(subsumption_resolution,[],[f101,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f101,plain,(
    ! [X2,X3] :
      ( ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X3)
      | sQ2_eqProxy(X2,X3)
      | r2_xboole_0(X2,X3)
      | sQ2_eqProxy(X3,X2)
      | r2_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f93,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | sQ2_eqProxy(X0,X1)
      | r2_xboole_0(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f93,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X3)
      | sQ2_eqProxy(X2,X3)
      | r2_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f73,f30])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f54,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f24,f25])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f21,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_xboole_0(sK1,sK0)
    & sK0 != sK1
    & ~ r2_xboole_0(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_xboole_0(X1,X0)
            & X0 != X1
            & ~ r2_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_xboole_0(X1,sK0)
          & sK0 != X1
          & ~ r2_xboole_0(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ r2_xboole_0(X1,sK0)
        & sK0 != X1
        & ~ r2_xboole_0(sK0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r2_xboole_0(sK1,sK0)
      & sK0 != sK1
      & ~ r2_xboole_0(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f23,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,plain,(
    ~ sQ2_eqProxy(sK0,sK1) ),
    inference(equality_proxy_replacement,[],[f22,f28])).

fof(f22,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:31:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (5422)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (5431)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (5422)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f20,f19,f29,f23,f21,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X2,X3] : (r2_xboole_0(X3,X2) | ~v3_ordinal1(X3) | r2_xboole_0(X2,X3) | sQ2_eqProxy(X3,X2) | ~v3_ordinal1(X2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f101,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~v3_ordinal1(X2) | ~v3_ordinal1(X3) | sQ2_eqProxy(X2,X3) | r2_xboole_0(X2,X3) | sQ2_eqProxy(X3,X2) | r2_xboole_0(X3,X2)) )),
% 0.21/0.47    inference(resolution,[],[f93,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | sQ2_eqProxy(X0,X1) | r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f27,f28])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X2,X3] : (r1_tarski(X3,X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(X3) | sQ2_eqProxy(X2,X3) | r2_xboole_0(X2,X3)) )),
% 0.21/0.47    inference(resolution,[],[f73,f30])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.47    inference(resolution,[],[f54,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X1,X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.47    inference(resolution,[],[f24,f25])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ~r2_xboole_0(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    (~r2_xboole_0(sK1,sK0) & sK0 != sK1 & ~r2_xboole_0(sK0,sK1) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r2_xboole_0(X1,sK0) & sK0 != X1 & ~r2_xboole_0(sK0,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X1] : (~r2_xboole_0(X1,sK0) & sK0 != X1 & ~r2_xboole_0(sK0,X1) & v3_ordinal1(X1)) => (~r2_xboole_0(sK1,sK0) & sK0 != sK1 & ~r2_xboole_0(sK0,sK1) & v3_ordinal1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ~r2_xboole_0(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~sQ2_eqProxy(sK0,sK1)),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f22,f28])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    sK0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v3_ordinal1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    v3_ordinal1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (5422)------------------------------
% 0.21/0.47  % (5422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5422)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (5422)Memory used [KB]: 6140
% 0.21/0.47  % (5422)Time elapsed: 0.054 s
% 0.21/0.47  % (5422)------------------------------
% 0.21/0.47  % (5422)------------------------------
% 0.21/0.48  % (5416)Success in time 0.113 s
%------------------------------------------------------------------------------
