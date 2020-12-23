%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 117 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 352 expanded)
%              Number of equality atoms :   15 (  80 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f32,f24,f158,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,X1))
      | sQ4_eqProxy(k1_xboole_0,X0)
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f27,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f158,plain,(
    r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1))) ),
    inference(resolution,[],[f118,f90])).

fof(f90,plain,(
    r1_tarski(k1_setfam_1(sK1),sK3(sK1,sK2(sK0,k1_setfam_1(sK1)))) ),
    inference(resolution,[],[f87,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f87,plain,(
    r2_hidden(sK3(sK1,sK2(sK0,k1_setfam_1(sK1))),sK1) ),
    inference(resolution,[],[f70,f22])).

fof(f22,plain,(
    r2_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    & k1_xboole_0 != sK0
    & r2_setfam_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        & k1_xboole_0 != X0
        & r2_setfam_1(X1,X0) )
   => ( ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
      & k1_xboole_0 != sK0
      & r2_setfam_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r2_setfam_1(X1,X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r2_setfam_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_setfam_1(X1,X0)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r2_setfam_1(X1,X0)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_setfam_1)).

fof(f70,plain,(
    ! [X1] :
      ( ~ r2_setfam_1(X1,sK0)
      | r2_hidden(sK3(X1,sK2(sK0,k1_setfam_1(sK1))),X1) ) ),
    inference(resolution,[],[f68,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(sK3(X0,X2),X0)
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(sK3(X0,X2),X2)
            & r2_hidden(sK3(X0,X2),X0) )
          | ~ r2_hidden(X2,X1) )
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).

fof(f20,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( r1_tarski(X3,X2)
          & r2_hidden(X3,X0) )
     => ( r1_tarski(sK3(X0,X2),X2)
        & r2_hidden(sK3(X0,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X3,X2)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(X2,X1) )
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r2_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X3,X2)
                  & r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X3,X2)
                  & r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_setfam_1)).

fof(f68,plain,(
    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f66,f32])).

fof(f66,plain,
    ( sQ4_eqProxy(k1_xboole_0,sK0)
    | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0) ),
    inference(resolution,[],[f34,f24])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | sQ4_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f26,f31])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3(sK1,sK2(sK0,k1_setfam_1(sK1))))
      | r1_tarski(X0,sK2(sK0,k1_setfam_1(sK1))) ) ),
    inference(resolution,[],[f97,f22])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_setfam_1(X0,sK0)
      | r1_tarski(X1,sK2(sK0,k1_setfam_1(sK1)))
      | ~ r1_tarski(X1,sK3(X0,sK2(sK0,k1_setfam_1(sK1)))) ) ),
    inference(resolution,[],[f69,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f69,plain,(
    ! [X0] :
      ( r1_tarski(sK3(X0,sK2(sK0,k1_setfam_1(sK1))),sK2(sK0,k1_setfam_1(sK1)))
      | ~ r2_setfam_1(X0,sK0) ) ),
    inference(resolution,[],[f68,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r1_tarski(sK3(X0,X2),X2)
      | ~ r2_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f24,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f32,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f23,f31])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (24071)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.43  % (24071)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f32,f24,f158,f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X1,sK2(X0,X1)) | sQ4_eqProxy(k1_xboole_0,X0) | r1_tarski(X1,k1_setfam_1(X0))) )),
% 0.20/0.43    inference(equality_proxy_replacement,[],[f27,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.43    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK2(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.20/0.43    inference(flattening,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    r1_tarski(k1_setfam_1(sK1),sK2(sK0,k1_setfam_1(sK1)))),
% 0.20/0.43    inference(resolution,[],[f118,f90])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    r1_tarski(k1_setfam_1(sK1),sK3(sK1,sK2(sK0,k1_setfam_1(sK1))))),
% 0.20/0.43    inference(resolution,[],[f87,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    r2_hidden(sK3(sK1,sK2(sK0,k1_setfam_1(sK1))),sK1)),
% 0.20/0.43    inference(resolution,[],[f70,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    r2_setfam_1(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r2_setfam_1(sK1,sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r2_setfam_1(X1,X0)) => (~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) & k1_xboole_0 != sK0 & r2_setfam_1(sK1,sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r2_setfam_1(X1,X0))),
% 0.20/0.43    inference(flattening,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r2_setfam_1(X1,X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1] : (r2_setfam_1(X1,X0) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.43    inference(negated_conjecture,[],[f5])).
% 0.20/0.43  fof(f5,conjecture,(
% 0.20/0.43    ! [X0,X1] : (r2_setfam_1(X1,X0) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_setfam_1)).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_setfam_1(X1,sK0) | r2_hidden(sK3(X1,sK2(sK0,k1_setfam_1(sK1))),X1)) )),
% 0.20/0.43    inference(resolution,[],[f68,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(sK3(X0,X2),X0) | ~r2_setfam_1(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : ((r1_tarski(sK3(X0,X2),X2) & r2_hidden(sK3(X0,X2),X0)) | ~r2_hidden(X2,X1)) | ~r2_setfam_1(X0,X1))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X2,X0] : (? [X3] : (r1_tarski(X3,X2) & r2_hidden(X3,X0)) => (r1_tarski(sK3(X0,X2),X2) & r2_hidden(sK3(X0,X2),X0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : (! [X2] : (? [X3] : (r1_tarski(X3,X2) & r2_hidden(X3,X0)) | ~r2_hidden(X2,X1)) | ~r2_setfam_1(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ! [X0,X1] : (r2_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X3,X2) & r2_hidden(X3,X0)) & r2_hidden(X2,X1)))),
% 0.20/0.43    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (r2_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X3,X2) & r2_hidden(X3,X0)) & r2_hidden(X2,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_setfam_1)).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f66,f32])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    sQ4_eqProxy(k1_xboole_0,sK0) | r2_hidden(sK2(sK0,k1_setfam_1(sK1)),sK0)),
% 0.20/0.43    inference(resolution,[],[f34,f24])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | sQ4_eqProxy(k1_xboole_0,X0) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.43    inference(equality_proxy_replacement,[],[f26,f31])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_tarski(X0,sK3(sK1,sK2(sK0,k1_setfam_1(sK1)))) | r1_tarski(X0,sK2(sK0,k1_setfam_1(sK1)))) )),
% 0.20/0.43    inference(resolution,[],[f97,f22])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_setfam_1(X0,sK0) | r1_tarski(X1,sK2(sK0,k1_setfam_1(sK1))) | ~r1_tarski(X1,sK3(X0,sK2(sK0,k1_setfam_1(sK1))))) )),
% 0.20/0.43    inference(resolution,[],[f69,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(flattening,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(sK3(X0,sK2(sK0,k1_setfam_1(sK1))),sK2(sK0,k1_setfam_1(sK1))) | ~r2_setfam_1(X0,sK0)) )),
% 0.20/0.43    inference(resolution,[],[f68,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r1_tarski(sK3(X0,X2),X2) | ~r2_setfam_1(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f21])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ~sQ4_eqProxy(k1_xboole_0,sK0)),
% 0.20/0.43    inference(equality_proxy_replacement,[],[f23,f31])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    k1_xboole_0 != sK0),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (24071)------------------------------
% 0.20/0.43  % (24071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (24071)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (24071)Memory used [KB]: 6140
% 0.20/0.43  % (24071)Time elapsed: 0.051 s
% 0.20/0.43  % (24071)------------------------------
% 0.20/0.43  % (24071)------------------------------
% 0.20/0.43  % (24065)Success in time 0.079 s
%------------------------------------------------------------------------------
