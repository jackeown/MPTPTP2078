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
% DateTime   : Thu Dec  3 12:48:23 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   33 (  59 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 198 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f18])).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).

% (937)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(X2,sK0)),k5_relat_1(sK1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(X2,sK0)),k5_relat_1(sK1,X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_relat_1)).

fof(f38,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f37,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f37,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),sK2) ),
    inference(subsumption_resolution,[],[f36,f18])).

fof(f36,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f35,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK2) ),
    inference(subsumption_resolution,[],[f34,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f33,f18])).

fof(f33,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f32,f26])).

fof(f26,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f32,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ r1_tarski(sK1,sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ r1_tarski(sK1,sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f20,f19])).

fof(f19,plain,(
    ~ r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 12:41:30 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.23/0.52  % (956)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (972)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (942)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (942)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(subsumption_resolution,[],[f38,f18])).
% 0.23/0.53  fof(f18,plain,(
% 0.23/0.53    v1_relat_1(sK2)),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,plain,(
% 0.23/0.53    (~r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).
% 0.23/0.53  % (937)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.53  fof(f12,plain,(
% 0.23/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK1,k7_relat_1(X2,sK0)),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f13,plain,(
% 0.23/0.53    ? [X2] : (~r1_tarski(k5_relat_1(sK1,k7_relat_1(X2,sK0)),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f7,plain,(
% 0.23/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f6])).
% 0.23/0.53  fof(f6,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))))),
% 0.23/0.53    inference(negated_conjecture,[],[f5])).
% 0.23/0.53  fof(f5,conjecture,(
% 0.23/0.53    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X1,k7_relat_1(X2,X0)),k5_relat_1(X1,X2))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_relat_1)).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    ~v1_relat_1(sK2)),
% 0.23/0.53    inference(resolution,[],[f37,f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,plain,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ~r1_tarski(k7_relat_1(sK2,sK0),sK2)),
% 0.23/0.53    inference(subsumption_resolution,[],[f36,f18])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(sK2)),
% 0.23/0.53    inference(resolution,[],[f35,f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,plain,(
% 0.23/0.53    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f2])).
% 0.23/0.53  fof(f2,axiom,(
% 0.23/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~r1_tarski(k7_relat_1(sK2,sK0),sK2)),
% 0.23/0.53    inference(subsumption_resolution,[],[f34,f17])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    v1_relat_1(sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK1)),
% 0.23/0.53    inference(subsumption_resolution,[],[f33,f18])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK1)),
% 0.23/0.53    inference(subsumption_resolution,[],[f32,f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.53    inference(equality_resolution,[],[f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.53    inference(flattening,[],[f15])).
% 0.23/0.53  fof(f15,plain,(
% 0.23/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.53    inference(nnf_transformation,[],[f1])).
% 0.23/0.53  fof(f1,axiom,(
% 0.23/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~r1_tarski(sK1,sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK1)),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f30])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~r1_tarski(sK1,sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK1)),
% 0.23/0.53    inference(resolution,[],[f20,f19])).
% 0.23/0.53  fof(f19,plain,(
% 0.23/0.53    ~r1_tarski(k5_relat_1(sK1,k7_relat_1(sK2,sK0)),k5_relat_1(sK1,sK2))),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f20,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.53    inference(flattening,[],[f8])).
% 0.23/0.53  fof(f8,plain,(
% 0.23/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.53    inference(ennf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (942)------------------------------
% 0.23/0.53  % (942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (942)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (942)Memory used [KB]: 6140
% 0.23/0.53  % (942)Time elapsed: 0.090 s
% 0.23/0.53  % (942)------------------------------
% 0.23/0.53  % (942)------------------------------
% 0.23/0.53  % (969)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.53  % (933)Success in time 0.149 s
%------------------------------------------------------------------------------
