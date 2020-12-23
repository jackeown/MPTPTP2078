%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 152 expanded)
%              Number of leaves         :    6 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  145 ( 609 expanded)
%              Number of equality atoms :   43 ( 232 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(subsumption_resolution,[],[f96,f75])).

fof(f75,plain,(
    r2_hidden(sK1(sK0,sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f72,f33])).

fof(f33,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f32,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f32,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f31,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(inner_rewriting,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( ( r1_xboole_0(sK0,sK0)
      & k1_xboole_0 != sK0 )
    | ( k1_xboole_0 = sK0
      & ~ r1_xboole_0(sK0,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).

fof(f7,plain,
    ( ? [X0] :
        ( ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
        | ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) )
   => ( ( r1_xboole_0(sK0,sK0)
        & k1_xboole_0 != sK0 )
      | ( k1_xboole_0 = sK0
        & ~ r1_xboole_0(sK0,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f72,plain,
    ( r2_hidden(sK1(sK0,sK0,sK0),sK0)
    | k1_xboole_0 = sK0 ),
    inference(factoring,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK1(sK0,sK0,X0),sK0)
      | k1_xboole_0 = X0
      | r2_hidden(sK1(sK0,sK0,X0),X0) ) ),
    inference(superposition,[],[f36,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f36,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f35,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,(
    r1_xboole_0(sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f33,f18])).

fof(f18,plain,
    ( k1_xboole_0 = sK0
    | r1_xboole_0(sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f96,plain,(
    ~ r2_hidden(sK1(sK0,sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f86,f33])).

fof(f86,plain,
    ( k1_xboole_0 = sK0
    | ~ r2_hidden(sK1(sK0,sK0,sK0),sK0) ),
    inference(resolution,[],[f75,f52])).

fof(f52,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK1(sK0,sK0,X2),sK0)
      | k1_xboole_0 = X2
      | ~ r2_hidden(sK1(sK0,sK0,X2),X2) ) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,(
    ! [X2] :
      ( k1_xboole_0 = X2
      | ~ r2_hidden(sK1(sK0,sK0,X2),sK0)
      | ~ r2_hidden(sK1(sK0,sK0,X2),sK0)
      | ~ r2_hidden(sK1(sK0,sK0,X2),X2) ) ),
    inference(superposition,[],[f36,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:04:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (17516)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (17504)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (17508)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (17511)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (17505)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (17505)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f75])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,sK0),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(subsumption_resolution,[],[f32,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f31,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0),
% 0.21/0.48    inference(inner_rewriting,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 != sK0 | ~r1_xboole_0(sK0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    (r1_xboole_0(sK0,sK0) & k1_xboole_0 != sK0) | (k1_xboole_0 = sK0 & ~r1_xboole_0(sK0,sK0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0))) => ((r1_xboole_0(sK0,sK0) & k1_xboole_0 != sK0) | (k1_xboole_0 = sK0 & ~r1_xboole_0(sK0,sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0,sK0,sK0),sK0) | k1_xboole_0 = sK0),
% 0.21/0.48    inference(factoring,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(sK0,sK0,X0),sK0) | k1_xboole_0 = X0 | r2_hidden(sK1(sK0,sK0,X0),X0)) )),
% 0.21/0.48    inference(superposition,[],[f36,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(rectify,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    k1_xboole_0 = k3_xboole_0(sK0,sK0)),
% 0.21/0.48    inference(resolution,[],[f35,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK0)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK0)),
% 0.21/0.48    inference(superposition,[],[f33,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | r1_xboole_0(sK0,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ~r2_hidden(sK1(sK0,sK0,sK0),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f33])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~r2_hidden(sK1(sK0,sK0,sK0),sK0)),
% 0.21/0.48    inference(resolution,[],[f75,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(sK1(sK0,sK0,X2),sK0) | k1_xboole_0 = X2 | ~r2_hidden(sK1(sK0,sK0,X2),X2)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(sK1(sK0,sK0,X2),sK0) | ~r2_hidden(sK1(sK0,sK0,X2),sK0) | ~r2_hidden(sK1(sK0,sK0,X2),X2)) )),
% 0.21/0.48    inference(superposition,[],[f36,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17505)------------------------------
% 0.21/0.48  % (17505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17505)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17505)Memory used [KB]: 1663
% 0.21/0.48  % (17505)Time elapsed: 0.068 s
% 0.21/0.48  % (17505)------------------------------
% 0.21/0.48  % (17505)------------------------------
% 0.21/0.49  % (17503)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (17511)Refutation not found, incomplete strategy% (17511)------------------------------
% 0.21/0.50  % (17511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17511)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17511)Memory used [KB]: 6012
% 0.21/0.50  % (17511)Time elapsed: 0.062 s
% 0.21/0.50  % (17511)------------------------------
% 0.21/0.50  % (17511)------------------------------
% 0.21/0.50  % (17507)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (17522)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (17522)Refutation not found, incomplete strategy% (17522)------------------------------
% 0.21/0.50  % (17522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17522)Memory used [KB]: 10490
% 0.21/0.50  % (17522)Time elapsed: 0.086 s
% 0.21/0.50  % (17522)------------------------------
% 0.21/0.50  % (17522)------------------------------
% 0.21/0.50  % (17501)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (17501)Refutation not found, incomplete strategy% (17501)------------------------------
% 0.21/0.50  % (17501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17501)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17501)Memory used [KB]: 6012
% 0.21/0.50  % (17501)Time elapsed: 0.082 s
% 0.21/0.50  % (17501)------------------------------
% 0.21/0.50  % (17501)------------------------------
% 0.21/0.50  % (17520)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (17514)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (17502)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (17514)Refutation not found, incomplete strategy% (17514)------------------------------
% 0.21/0.51  % (17514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17514)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17514)Memory used [KB]: 6012
% 0.21/0.51  % (17514)Time elapsed: 0.002 s
% 0.21/0.51  % (17514)------------------------------
% 0.21/0.51  % (17514)------------------------------
% 0.21/0.51  % (17502)Refutation not found, incomplete strategy% (17502)------------------------------
% 0.21/0.51  % (17502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17502)Memory used [KB]: 10490
% 0.21/0.51  % (17502)Time elapsed: 0.092 s
% 0.21/0.51  % (17502)------------------------------
% 0.21/0.51  % (17502)------------------------------
% 0.21/0.51  % (17500)Success in time 0.146 s
%------------------------------------------------------------------------------
