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
% DateTime   : Thu Dec  3 12:55:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 228 expanded)
%              Number of equality atoms :   45 (  66 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(subsumption_resolution,[],[f55,f26])).

fof(f26,plain,(
    k1_xboole_0 != k1_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k1_wellord1(sK1,sK0)
    & ~ r2_hidden(sK0,k3_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != k1_wellord1(X1,X0)
        & ~ r2_hidden(X0,k3_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_xboole_0 != k1_wellord1(sK1,sK0)
      & ~ r2_hidden(sK0,k3_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

fof(f55,plain,(
    k1_xboole_0 = k1_wellord1(sK1,sK0) ),
    inference(resolution,[],[f53,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f53,plain,(
    ! [X6] : r1_tarski(k1_wellord1(sK1,sK0),X6) ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    ~ r2_hidden(sK0,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_relat_1(sK1))
      | r1_tarski(k1_wellord1(sK1,X0),X1) ) ),
    inference(subsumption_resolution,[],[f47,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(sK1,X0),X1)
      | r2_hidden(X0,k3_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f46,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(k1_wellord1(sK1,X0),X1),X0),sK1)
      | r1_tarski(k1_wellord1(sK1,X0),X1) ) ),
    inference(resolution,[],[f45,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(sK1,X1))
      | r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                | sK2(X0,X1,X2) = X1
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                  & sK2(X0,X1,X2) != X1 )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
          | sK2(X0,X1,X2) = X1
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
            & sK2(X0,X1,X2) != X1 )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:43:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (27732)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.48  % (27732)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f55,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    k1_xboole_0 != k1_wellord1(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    k1_xboole_0 != k1_wellord1(sK1,sK0) & ~r2_hidden(sK0,k3_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1)) => (k1_xboole_0 != k1_wellord1(sK1,sK0) & ~r2_hidden(sK0,k3_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1] : ((k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    k1_xboole_0 = k1_wellord1(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f53,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X6] : (r1_tarski(k1_wellord1(sK1,sK0),X6)) )),
% 0.20/0.48    inference(resolution,[],[f49,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k3_relat_1(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X0,k3_relat_1(sK1)) | r1_tarski(k1_wellord1(sK1,X0),X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f47,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_wellord1(sK1,X0),X1) | r2_hidden(X0,k3_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.20/0.48    inference(resolution,[],[f46,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(k1_wellord1(sK1,X0),X1),X0),sK1) | r1_tarski(k1_wellord1(sK1,X0),X1)) )),
% 0.20/0.48    inference(resolution,[],[f45,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.20/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK1,X1)) | r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 0.20/0.48    inference(resolution,[],[f39,f24])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(rectify,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (27732)------------------------------
% 0.20/0.48  % (27732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (27732)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (27732)Memory used [KB]: 6268
% 0.20/0.48  % (27732)Time elapsed: 0.085 s
% 0.20/0.48  % (27732)------------------------------
% 0.20/0.48  % (27732)------------------------------
% 0.20/0.48  % (27723)Success in time 0.118 s
%------------------------------------------------------------------------------
