%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  79 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 248 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13284)WARNING: option uwaf not known.
% (13289)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% (13284)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% (13274)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% (13275)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% (13281)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% (13290)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
fof(f51,plain,(
    $false ),
    inference(subsumption_resolution,[],[f50,f26])).

fof(f26,plain,(
    ~ r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(sK2))
    & r1_setfam_1(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f7,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
        & r1_setfam_1(X0,X1) )
   => ( ~ r1_tarski(k3_tarski(sK1),k3_tarski(sK2))
      & r1_setfam_1(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f50,plain,(
    r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(sK2))
    | r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK1,X0),k3_tarski(sK2))
      | r1_tarski(k3_tarski(sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(sK1),X0)
      | r1_tarski(sK3(sK1,X0),k3_tarski(sK2))
      | r1_tarski(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f45,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(sK5(sK2,sK3(sK1,X0)),k3_tarski(sK2))
      | r1_tarski(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(sK5(sK2,X0),k3_tarski(sK2)) ) ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    ! [X4,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(sK5(X0,X4),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( ~ r1_tarski(sK4(X0,X1),X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(sK4(X0,X1),X1) ) )
      & ( ! [X4] :
            ( ( r1_tarski(X4,sK5(X0,X4))
              & r2_hidden(sK5(X0,X4),X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f20,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X0) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK4(X0,X1),X3)
            | ~ r2_hidden(X3,X0) )
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( r1_tarski(X4,X5)
          & r2_hidden(X5,X0) )
     => ( r1_tarski(X4,sK5(X0,X4))
        & r2_hidden(sK5(X0,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X0) )
            & r2_hidden(X2,X1) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( r1_tarski(X4,X5)
                & r2_hidden(X5,X0) )
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( r1_tarski(X2,X3)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X0) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f37,plain,(
    sP0(sK2,sK1) ),
    inference(resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_setfam_1(X0,X1)
        | ~ sP0(X1,X0) )
      & ( sP0(X1,X0)
        | ~ r1_setfam_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> sP0(X1,X0) ) ),
    inference(definition_folding,[],[f10,f13])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f25,plain,(
    r1_setfam_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK5(sK2,sK3(sK1,X0)),X1)
      | r1_tarski(k3_tarski(sK1),X0)
      | r1_tarski(sK3(sK1,X0),X1) ) ),
    inference(resolution,[],[f42,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
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

fof(f42,plain,(
    ! [X0] :
      ( r1_tarski(sK3(sK1,X0),sK5(sK2,sK3(sK1,X0)))
      | r1_tarski(k3_tarski(sK1),X0) ) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r1_tarski(X1,sK5(sK2,X1)) ) ),
    inference(resolution,[],[f37,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X4,X1)
      | r1_tarski(X4,sK5(X0,X4)) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (13282)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (13276)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.48  % (13287)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.49  % (13283)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (13279)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.49  % (13283)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  % (13284)WARNING: option uwaf not known.
% 0.21/0.49  % (13289)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.49  % (13284)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.49  % (13274)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (13275)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.50  % (13281)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.50  % (13290)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f50,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ~r1_tarski(k3_tarski(sK1),k3_tarski(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ~r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) & r1_setfam_1(sK1,sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f7,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_setfam_1(X0,X1)) => (~r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) & r1_setfam_1(sK1,sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_setfam_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    r1_tarski(k3_tarski(sK1),k3_tarski(sK2))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) | r1_tarski(k3_tarski(sK1),k3_tarski(sK2))),
% 0.21/0.50    inference(resolution,[],[f47,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(sK3(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(sK3(sK1,X0),k3_tarski(sK2)) | r1_tarski(k3_tarski(sK1),X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k3_tarski(sK1),X0) | r1_tarski(sK3(sK1,X0),k3_tarski(sK2)) | r1_tarski(k3_tarski(sK1),X0)) )),
% 0.21/0.50    inference(resolution,[],[f45,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(sK5(sK2,sK3(sK1,X0)),k3_tarski(sK2)) | r1_tarski(k3_tarski(sK1),X0)) )),
% 0.21/0.50    inference(resolution,[],[f41,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(sK5(sK2,X0),k3_tarski(sK2))) )),
% 0.21/0.50    inference(resolution,[],[f39,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(sK2,X0),sK2) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.50    inference(resolution,[],[f37,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (~sP0(X0,X1) | ~r2_hidden(X4,X1) | r2_hidden(sK5(X0,X4),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (~r1_tarski(sK4(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK4(X0,X1),X1))) & (! [X4] : ((r1_tarski(X4,sK5(X0,X4)) & r2_hidden(sK5(X0,X4),X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f20,f22,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1)) => (! [X3] : (~r1_tarski(sK4(X0,X1),X3) | ~r2_hidden(X3,X0)) & r2_hidden(sK4(X0,X1),X1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X4,X0] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) => (r1_tarski(X4,sK5(X0,X4)) & r2_hidden(sK5(X0,X4),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0)) & r2_hidden(X2,X1))) & (! [X4] : (? [X5] : (r1_tarski(X4,X5) & r2_hidden(X5,X0)) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0))) & (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~sP0(X1,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    sP0(sK2,sK1)),
% 0.21/0.50    inference(resolution,[],[f25,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_setfam_1(X0,X1) | sP0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_setfam_1(X0,X1) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~r1_setfam_1(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> sP0(X1,X0))),
% 0.21/0.50    inference(definition_folding,[],[f10,f13])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    r1_setfam_1(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(sK5(sK2,sK3(sK1,X0)),X1) | r1_tarski(k3_tarski(sK1),X0) | r1_tarski(sK3(sK1,X0),X1)) )),
% 0.21/0.50    inference(resolution,[],[f42,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(sK3(sK1,X0),sK5(sK2,sK3(sK1,X0))) | r1_tarski(k3_tarski(sK1),X0)) )),
% 0.21/0.50    inference(resolution,[],[f40,f28])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(X1,sK5(sK2,X1))) )),
% 0.21/0.50    inference(resolution,[],[f37,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (~sP0(X0,X1) | ~r2_hidden(X4,X1) | r1_tarski(X4,sK5(X0,X4))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (13283)------------------------------
% 0.21/0.50  % (13283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13283)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (13283)Memory used [KB]: 9850
% 0.21/0.50  % (13283)Time elapsed: 0.077 s
% 0.21/0.50  % (13283)------------------------------
% 0.21/0.50  % (13283)------------------------------
% 0.21/0.50  % (13280)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.50  % (13273)Success in time 0.139 s
%------------------------------------------------------------------------------
