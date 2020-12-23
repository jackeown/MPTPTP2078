%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  95 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  144 ( 376 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f113,f115])).

fof(f115,plain,(
    ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f22,f112])).

fof(f112,plain,(
    r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) ),
    inference(resolution,[],[f111,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f111,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f82,f21])).

fof(f21,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
      | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) )
    & r2_hidden(sK1,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
            & r2_hidden(X1,X0) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0)) )
          & r2_hidden(X1,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
          | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0)) )
        & r2_hidden(X1,sK0) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
        | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) )
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ) ),
    inference(superposition,[],[f43,f79])).

fof(f79,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f23,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f43,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X6,k4_xboole_0(X5,k4_xboole_0(X5,X4)))
      | r2_hidden(X6,X4) ) ),
    inference(superposition,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f33,f32,f32])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f22,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
    | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,(
    r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(resolution,[],[f111,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.35  % CPULimit   : 60
% 0.21/0.35  % WCLimit    : 600
% 0.21/0.35  % DateTime   : Tue Dec  1 18:05:36 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.55  % (32316)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (32290)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (32304)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (32290)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f113,f115])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.21/0.56    inference(subsumption_resolution,[],[f22,f112])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))),
% 0.21/0.56    inference(resolution,[],[f111,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    r2_hidden(sK1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.56    inference(resolution,[],[f82,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    r2_hidden(sK1,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ((~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) & r2_hidden(sK1,sK0)) & v1_relat_1(sK0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13,f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0)) => (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0))) & r2_hidden(X1,sK0)) & v1_relat_1(sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0))) & r2_hidden(X1,sK0)) => ((~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) & r2_hidden(sK1,sK0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f7])).
% 0.21/0.56  fof(f7,conjecture,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) )),
% 0.21/0.56    inference(superposition,[],[f43,f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.21/0.56    inference(resolution,[],[f36,f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    v1_relat_1(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_relat_1(X0) | k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f23,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X6,X4,X5] : (~r2_hidden(X6,k4_xboole_0(X5,k4_xboole_0(X5,X4))) | r2_hidden(X6,X4)) )),
% 0.21/0.56    inference(superposition,[],[f40,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f33,f32,f32])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.56    inference(rectify,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.21/0.56    inference(resolution,[],[f111,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (32290)------------------------------
% 0.21/0.56  % (32290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32290)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (32290)Memory used [KB]: 6268
% 0.21/0.56  % (32290)Time elapsed: 0.140 s
% 0.21/0.56  % (32290)------------------------------
% 0.21/0.56  % (32290)------------------------------
% 0.21/0.56  % (32289)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (32314)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (32285)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (32315)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (32306)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (32297)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (32294)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (32308)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (32288)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.58  % (32312)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.58  % (32281)Success in time 0.22 s
%------------------------------------------------------------------------------
