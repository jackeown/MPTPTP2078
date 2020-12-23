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
% DateTime   : Thu Dec  3 12:56:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 358 expanded)
%              Number of leaves         :    7 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  208 (2553 expanded)
%              Number of equality atoms :   17 ( 269 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97,f42])).

fof(f42,plain,(
    ~ r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X3] :
      ( sK1 != X3
      | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    & ! [X3] :
        ( ( sK1 != X3
          & r2_hidden(k4_tarski(X3,sK1),sK2) )
        | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        & ! [X3] :
            ( ( X1 != X3
              & r2_hidden(k4_tarski(X3,X1),X2) )
            | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
      & ! [X3] :
          ( ( sK1 != X3
            & r2_hidden(k4_tarski(X3,sK1),sK2) )
          | ~ r2_hidden(X3,k1_wellord1(sK2,sK0)) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      & ! [X3] :
          ( ( X1 != X3
            & r2_hidden(k4_tarski(X3,X1),X2) )
          | ~ r2_hidden(X3,k1_wellord1(X2,X0)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( ! [X3] :
                ( r2_hidden(X3,k1_wellord1(X2,X0))
               => ( X1 != X3
                  & r2_hidden(k4_tarski(X3,X1),X2) ) )
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( ! [X3] :
              ( r2_hidden(X3,k1_wellord1(X2,X0))
             => ( X1 != X3
                & r2_hidden(k4_tarski(X3,X1),X2) ) )
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => r2_hidden(k4_tarski(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

fof(f97,plain,(
    r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    inference(backward_demodulation,[],[f63,f92])).

fof(f92,plain,(
    sK1 = sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f26,f28,f79,f64,f85,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_wellord1(X2,X1))
      | X0 = X1
      | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
            & X0 != X1 ) )
        & ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
            & X0 != X1 ) )
        & ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
            | X0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

fof(f85,plain,(
    r1_tarski(k1_wellord1(sK2,sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),k1_wellord1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f26,f28,f73,f79,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

fof(f73,plain,(
    r2_hidden(k4_tarski(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f63,f29])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_wellord1(sK2,sK0))
      | r2_hidden(k4_tarski(X3,sK1),sK2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ~ r2_hidden(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f47,plain,(
    ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f31,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    r2_hidden(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k3_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f25,f73,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f28,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    r2_hidden(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:01:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.21/0.48  % (14884)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.49  % (14881)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (14888)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.49  % (14893)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (14907)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (14907)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f97,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 0.21/0.50    inference(equality_resolution,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X3] : (sK1 != X3 | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ~r2_hidden(k4_tarski(sK0,sK1),sK2) & ! [X3] : ((sK1 != X3 & r2_hidden(k4_tarski(X3,sK1),sK2)) | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => (~r2_hidden(k4_tarski(sK0,sK1),sK2) & ! [X3] : ((sK1 != X3 & r2_hidden(k4_tarski(X3,sK1),sK2)) | ~r2_hidden(X3,k1_wellord1(sK2,sK0))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r2_hidden(k4_tarski(X0,X1),X2) & ! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f7])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~r2_hidden(k4_tarski(X0,X1),X2) & (! [X3] : ((X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2)) | ~r2_hidden(X3,k1_wellord1(X2,X0))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((! [X3] : (r2_hidden(X3,k1_wellord1(X2,X0)) => (X1 != X3 & r2_hidden(k4_tarski(X3,X1),X2))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => r2_hidden(k4_tarski(X0,X1),X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    r2_hidden(sK1,k1_wellord1(sK2,sK0))),
% 0.21/0.50    inference(backward_demodulation,[],[f63,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    sK1 = sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f25,f26,f28,f79,f64,f85,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1 | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | (~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1)) & (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1 | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | (~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1)) & ((r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    r1_tarski(k1_wellord1(sK2,sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),k1_wellord1(sK2,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f25,f26,f28,f73,f79,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    r2_hidden(k4_tarski(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),sK1),sK2)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f63,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,k1_wellord1(sK2,sK0)) | r2_hidden(k4_tarski(X3,sK1),sK2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ~r2_hidden(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f47,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f25,f26,f27,f28,f31,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ~r2_hidden(k4_tarski(sK0,sK1),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    r2_hidden(sK0,k3_relat_1(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    r2_hidden(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k3_relat_1(sK2))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f25,f73,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    r2_hidden(sK1,k3_relat_1(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    v2_wellord1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    r2_hidden(sK3(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f47,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (14907)------------------------------
% 0.21/0.50  % (14907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14907)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (14907)Memory used [KB]: 10746
% 0.21/0.50  % (14907)Time elapsed: 0.109 s
% 0.21/0.50  % (14907)------------------------------
% 0.21/0.50  % (14907)------------------------------
% 0.21/0.50  % (14880)Success in time 0.154 s
%------------------------------------------------------------------------------
