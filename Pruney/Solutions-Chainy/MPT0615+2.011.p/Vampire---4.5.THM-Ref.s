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
% DateTime   : Thu Dec  3 12:51:44 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 210 expanded)
%              Number of leaves         :    8 (  56 expanded)
%              Depth                    :   20
%              Number of atoms          :  159 ( 948 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(subsumption_resolution,[],[f182,f168])).

% (1534)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f168,plain,(
    r1_tarski(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( r1_tarski(sK0,sK1)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f164,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f164,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0,sK1),sK0)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f159,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f159,plain,(
    ! [X14] :
      ( r2_hidden(X14,sK1)
      | ~ r2_hidden(X14,sK0) ) ),
    inference(subsumption_resolution,[],[f155,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f155,plain,(
    ! [X14] :
      ( ~ r2_hidden(X14,sK0)
      | r2_hidden(X14,sK1)
      | r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f59,f25])).

fof(f25,plain,
    ( r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | r1_tarski(sK0,sK1) ),
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

% (1533)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
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
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r1_tarski(X0,X1)
          <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
            <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).

fof(f59,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,k7_relat_1(sK1,X4))
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X2,sK1) ) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k7_relat_1(sK1,X1))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f40,f30])).

fof(f40,plain,(
    ! [X5] : r1_tarski(k7_relat_1(sK1,X5),sK1) ),
    inference(resolution,[],[f24,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f182,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f176,f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f176,plain,(
    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) ),
    inference(superposition,[],[f172,f121])).

fof(f121,plain,(
    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f118,f35])).

fof(f35,plain,(
    ! [X4] :
      ( ~ r1_tarski(k1_relat_1(sK0),X4)
      | sK0 = k7_relat_1(sK0,X4) ) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f118,plain,
    ( sK0 = k7_relat_1(sK0,k1_relat_1(sK0))
    | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    inference(resolution,[],[f81,f31])).

fof(f81,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(k1_relat_1(sK0),X1),X1)
      | sK0 = k7_relat_1(sK0,X1) ) ),
    inference(resolution,[],[f35,f32])).

fof(f172,plain,(
    ! [X1] : r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f171,f23])).

fof(f171,plain,(
    ! [X1] :
      ( r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(sK1,X1))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f24])).

fof(f170,plain,(
    ! [X1] :
      ( r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f168,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.56  % (1550)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.56  % (1542)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.57  % (1530)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.57  % (1550)Refutation found. Thanks to Tanya!
% 1.49/0.57  % SZS status Theorem for theBenchmark
% 1.49/0.57  % SZS output start Proof for theBenchmark
% 1.49/0.57  fof(f187,plain,(
% 1.49/0.57    $false),
% 1.49/0.57    inference(subsumption_resolution,[],[f182,f168])).
% 1.49/0.57  % (1534)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.57  fof(f168,plain,(
% 1.49/0.57    r1_tarski(sK0,sK1)),
% 1.49/0.57    inference(duplicate_literal_removal,[],[f166])).
% 1.49/0.57  fof(f166,plain,(
% 1.49/0.57    r1_tarski(sK0,sK1) | r1_tarski(sK0,sK1)),
% 1.49/0.57    inference(resolution,[],[f164,f31])).
% 1.49/0.57  fof(f31,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f22])).
% 1.49/0.57  fof(f22,plain,(
% 1.49/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 1.49/0.57  fof(f21,plain,(
% 1.49/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f20,plain,(
% 1.49/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.57    inference(rectify,[],[f19])).
% 1.49/0.57  fof(f19,plain,(
% 1.49/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.57    inference(nnf_transformation,[],[f13])).
% 1.49/0.57  fof(f13,plain,(
% 1.49/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f1])).
% 1.49/0.57  fof(f1,axiom,(
% 1.49/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.57  fof(f164,plain,(
% 1.49/0.57    ( ! [X0] : (~r2_hidden(sK2(X0,sK1),sK0) | r1_tarski(X0,sK1)) )),
% 1.49/0.57    inference(resolution,[],[f159,f32])).
% 1.49/0.57  fof(f32,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f22])).
% 1.49/0.57  fof(f159,plain,(
% 1.49/0.57    ( ! [X14] : (r2_hidden(X14,sK1) | ~r2_hidden(X14,sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f155,f30])).
% 1.49/0.57  fof(f30,plain,(
% 1.49/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f22])).
% 1.49/0.57  fof(f155,plain,(
% 1.49/0.57    ( ! [X14] : (~r2_hidden(X14,sK0) | r2_hidden(X14,sK1) | r1_tarski(sK0,sK1)) )),
% 1.49/0.57    inference(resolution,[],[f59,f25])).
% 1.49/0.57  fof(f25,plain,(
% 1.49/0.57    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)),
% 1.49/0.57    inference(cnf_transformation,[],[f18])).
% 1.49/0.57  fof(f18,plain,(
% 1.49/0.57    ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).
% 1.49/0.57  fof(f16,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  % (1533)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.57  fof(f17,plain,(
% 1.49/0.57    ? [X1] : ((~r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | ~r1_tarski(sK0,X1)) & (r1_tarski(sK0,k7_relat_1(X1,k1_relat_1(sK0))) | r1_tarski(sK0,X1)) & v1_relat_1(X1)) => ((~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)) & (r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | r1_tarski(sK0,sK1)) & v1_relat_1(sK1))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f15,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : ((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.49/0.57    inference(flattening,[],[f14])).
% 1.49/0.57  fof(f14,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : (((~r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) | r1_tarski(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.49/0.57    inference(nnf_transformation,[],[f7])).
% 1.49/0.57  fof(f7,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : ((r1_tarski(X0,X1) <~> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f6])).
% 1.49/0.57  fof(f6,negated_conjecture,(
% 1.49/0.57    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.49/0.57    inference(negated_conjecture,[],[f5])).
% 1.49/0.57  fof(f5,conjecture,(
% 1.49/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t219_relat_1)).
% 1.49/0.57  fof(f59,plain,(
% 1.49/0.57    ( ! [X4,X2,X3] : (~r1_tarski(X3,k7_relat_1(sK1,X4)) | ~r2_hidden(X2,X3) | r2_hidden(X2,sK1)) )),
% 1.49/0.57    inference(resolution,[],[f46,f30])).
% 1.49/0.57  fof(f46,plain,(
% 1.49/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k7_relat_1(sK1,X1)) | r2_hidden(X0,sK1)) )),
% 1.49/0.57    inference(resolution,[],[f40,f30])).
% 1.49/0.57  fof(f40,plain,(
% 1.49/0.57    ( ! [X5] : (r1_tarski(k7_relat_1(sK1,X5),sK1)) )),
% 1.49/0.57    inference(resolution,[],[f24,f27])).
% 1.49/0.57  fof(f27,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f8])).
% 1.49/0.57  fof(f8,plain,(
% 1.49/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.49/0.57    inference(ennf_transformation,[],[f3])).
% 1.49/0.57  fof(f3,axiom,(
% 1.49/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.49/0.57  fof(f24,plain,(
% 1.49/0.57    v1_relat_1(sK1)),
% 1.49/0.57    inference(cnf_transformation,[],[f18])).
% 1.49/0.57  fof(f182,plain,(
% 1.49/0.57    ~r1_tarski(sK0,sK1)),
% 1.49/0.57    inference(resolution,[],[f176,f26])).
% 1.49/0.57  fof(f26,plain,(
% 1.49/0.57    ~r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0))) | ~r1_tarski(sK0,sK1)),
% 1.49/0.57    inference(cnf_transformation,[],[f18])).
% 1.49/0.57  fof(f176,plain,(
% 1.49/0.57    r1_tarski(sK0,k7_relat_1(sK1,k1_relat_1(sK0)))),
% 1.49/0.57    inference(superposition,[],[f172,f121])).
% 1.49/0.57  fof(f121,plain,(
% 1.49/0.57    sK0 = k7_relat_1(sK0,k1_relat_1(sK0))),
% 1.49/0.57    inference(subsumption_resolution,[],[f118,f35])).
% 1.49/0.57  fof(f35,plain,(
% 1.49/0.57    ( ! [X4] : (~r1_tarski(k1_relat_1(sK0),X4) | sK0 = k7_relat_1(sK0,X4)) )),
% 1.49/0.57    inference(resolution,[],[f23,f28])).
% 1.49/0.57  fof(f28,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f10])).
% 1.49/0.57  fof(f10,plain,(
% 1.49/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.49/0.57    inference(flattening,[],[f9])).
% 1.49/0.57  fof(f9,plain,(
% 1.49/0.57    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.57    inference(ennf_transformation,[],[f4])).
% 1.49/0.57  fof(f4,axiom,(
% 1.49/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.49/0.57  fof(f23,plain,(
% 1.49/0.57    v1_relat_1(sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f18])).
% 1.49/0.57  fof(f118,plain,(
% 1.49/0.57    sK0 = k7_relat_1(sK0,k1_relat_1(sK0)) | r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 1.49/0.57    inference(resolution,[],[f81,f31])).
% 1.49/0.57  fof(f81,plain,(
% 1.49/0.57    ( ! [X1] : (~r2_hidden(sK2(k1_relat_1(sK0),X1),X1) | sK0 = k7_relat_1(sK0,X1)) )),
% 1.49/0.57    inference(resolution,[],[f35,f32])).
% 1.49/0.57  fof(f172,plain,(
% 1.49/0.57    ( ! [X1] : (r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(sK1,X1))) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f171,f23])).
% 1.49/0.57  fof(f171,plain,(
% 1.49/0.57    ( ! [X1] : (r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(sK1,X1)) | ~v1_relat_1(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f170,f24])).
% 1.49/0.57  fof(f170,plain,(
% 1.49/0.57    ( ! [X1] : (r1_tarski(k7_relat_1(sK0,X1),k7_relat_1(sK1,X1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)) )),
% 1.49/0.57    inference(resolution,[],[f168,f29])).
% 1.49/0.57  fof(f29,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f12])).
% 1.49/0.57  fof(f12,plain,(
% 1.49/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.49/0.57    inference(flattening,[],[f11])).
% 1.49/0.57  fof(f11,plain,(
% 1.49/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.49/0.57    inference(ennf_transformation,[],[f2])).
% 1.49/0.57  fof(f2,axiom,(
% 1.49/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (1550)------------------------------
% 1.49/0.57  % (1550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (1550)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (1550)Memory used [KB]: 1791
% 1.49/0.57  % (1550)Time elapsed: 0.091 s
% 1.49/0.57  % (1550)------------------------------
% 1.49/0.57  % (1550)------------------------------
% 1.49/0.58  % (1528)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.58  % (1526)Success in time 0.222 s
%------------------------------------------------------------------------------
