%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  94 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  109 ( 283 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48,f44])).

fof(f44,plain,(
    r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f39,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        & v1_relat_1(X0) )
   => ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f39,plain,
    ( r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f35,plain,(
    r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0) ),
    inference(resolution,[],[f32,f19])).

fof(f19,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | r2_hidden(k4_tarski(sK1(sK0,X0),sK2(sK0,X0)),sK0) ) ),
    inference(resolution,[],[f21,f18])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f48,plain,(
    ~ r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f47,f19])).

fof(f47,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f46,plain,
    ( ~ v1_relat_1(sK0)
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,k2_zfmisc_1(X1,X2)),X2)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X1) ) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f38,f18])).

fof(f38,plain,
    ( r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (9481)WARNING: option uwaf not known.
% 0.22/0.46  % (9491)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.46  % (9489)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.46  % (9481)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.46  % (9481)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f48,f44])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))),
% 0.22/0.46    inference(subsumption_resolution,[],[f39,f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    v1_relat_1(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ? [X0] : (~r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) & v1_relat_1(X0)) => (~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f6,plain,(
% 0.22/0.46    ? [X0] : (~r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) & v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,negated_conjecture,(
% 0.22/0.46    ~! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.46    inference(negated_conjecture,[],[f4])).
% 0.22/0.46  fof(f4,conjecture,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.46    inference(resolution,[],[f35,f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(flattening,[],[f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    r2_hidden(k4_tarski(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),sK0)),
% 0.22/0.46    inference(resolution,[],[f32,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ~r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(sK0,X0) | r2_hidden(k4_tarski(sK1(sK0,X0),sK2(sK0,X0)),sK0)) )),
% 0.22/0.46    inference(resolution,[],[f21,f18])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(rectify,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(nnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    ~r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))),
% 0.22/0.46    inference(subsumption_resolution,[],[f47,f19])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))),
% 0.22/0.46    inference(subsumption_resolution,[],[f46,f18])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    ~v1_relat_1(sK0) | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~r2_hidden(sK1(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k1_relat_1(sK0))),
% 0.22/0.46    inference(resolution,[],[f43,f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,k2_zfmisc_1(X1,X2)),X2) | ~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X1)) )),
% 0.22/0.46    inference(resolution,[],[f22,f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.46    inference(flattening,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.46    inference(nnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0))),
% 0.22/0.46    inference(subsumption_resolution,[],[f38,f18])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    r2_hidden(sK2(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),k2_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 0.22/0.46    inference(resolution,[],[f35,f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f9])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (9481)------------------------------
% 0.22/0.46  % (9481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (9481)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (9481)Memory used [KB]: 895
% 0.22/0.46  % (9481)Time elapsed: 0.049 s
% 0.22/0.46  % (9481)------------------------------
% 0.22/0.46  % (9481)------------------------------
% 0.22/0.47  % (9470)Success in time 0.104 s
%------------------------------------------------------------------------------
