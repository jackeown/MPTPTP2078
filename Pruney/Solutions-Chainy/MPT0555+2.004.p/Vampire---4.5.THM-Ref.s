%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 182 expanded)
%              Number of leaves         :    8 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  159 ( 819 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f54,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52,f45])).

fof(f45,plain,(
    r2_hidden(k4_tarski(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),sK2) ),
    inference(unit_resulting_resolution,[],[f25,f43,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f43,plain,(
    r2_hidden(k4_tarski(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f23,f36,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
            & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f36,plain,(
    r2_hidden(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),k9_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
            & r1_tarski(X1,X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0))
          & r1_tarski(sK1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0))
        & r1_tarski(sK1,X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ~ r2_hidden(k4_tarski(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),sK2) ),
    inference(unit_resulting_resolution,[],[f24,f37,f40,f44,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    r2_hidden(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f41,f29])).

fof(f41,plain,(
    r2_hidden(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f36,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f23,f24,f25,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f40,plain,(
    r2_hidden(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f23,f36,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ~ r2_hidden(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (9937)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.20/0.47  % (9946)WARNING: option uwaf not known.
% 0.20/0.47  % (9946)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.48  % (9949)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.48  % (9950)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.48  % (9938)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.48  % (9950)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (9947)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f52,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f25,f43,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),sK1)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f23,f36,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK4(X0,X1,X2),X0),X2) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(rectify,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    r2_hidden(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),k9_relat_1(sK1,sK0))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f26,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X2] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_relat_1)).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    r1_tarski(sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ~r2_hidden(k4_tarski(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f24,f37,f40,f44,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    r2_hidden(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),k1_relat_1(sK2))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f38,f41,f29])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    r2_hidden(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),k1_relat_1(sK1))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f23,f36,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    r1_tarski(k1_relat_1(sK1),k1_relat_1(sK2))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f23,f24,f25,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    r2_hidden(sK4(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),sK0,sK1),sK0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f23,f36,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ~r2_hidden(sK3(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)),k9_relat_1(sK2,sK0))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f26,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (9950)------------------------------
% 0.20/0.48  % (9950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9950)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (9950)Memory used [KB]: 5373
% 0.20/0.48  % (9950)Time elapsed: 0.034 s
% 0.20/0.48  % (9950)------------------------------
% 0.20/0.48  % (9950)------------------------------
% 0.20/0.48  % (9954)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (9942)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % (9948)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.20/0.48  % (9941)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (9935)Success in time 0.128 s
%------------------------------------------------------------------------------
