%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 117 expanded)
%              Number of leaves         :    7 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 562 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f65,f59,f68,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f68,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK5(sK1,sK3,sK2)),k2_zfmisc_1(X0,sK3)) ),
    inference(unit_resulting_resolution,[],[f51,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f51,plain,(
    r1_tarski(sK5(sK1,sK3,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f49,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tarski(sK5(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2)))
        & r1_tarski(sK5(X0,X1,X2),X1)
        & v1_finset_1(sK5(X0,X1,X2))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X1)
          & v1_finset_1(X4)
          & r1_tarski(X3,X2)
          & v1_finset_1(X3) )
     => ( r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2)))
        & r1_tarski(sK5(X0,X1,X2),X1)
        & v1_finset_1(sK5(X0,X1,X2))
        & r1_tarski(sK4(X0,X1,X2),X2)
        & v1_finset_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X1)
          & v1_finset_1(X4)
          & r1_tarski(X3,X2)
          & v1_finset_1(X3) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X2,X1] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X2,X1] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f49,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f19,f20,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X2,X1)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(definition_folding,[],[f10,f11])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

fof(f20,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK1,k2_zfmisc_1(X3,sK3))
        | ~ r1_tarski(X3,sK2)
        | ~ v1_finset_1(X3) )
    & r1_tarski(sK1,k2_zfmisc_1(sK2,sK3))
    & v1_finset_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
            | ~ r1_tarski(X3,X1)
            | ~ v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) )
   => ( ! [X3] :
          ( ~ r1_tarski(sK1,k2_zfmisc_1(X3,sK3))
          | ~ r1_tarski(X3,sK2)
          | ~ v1_finset_1(X3) )
      & r1_tarski(sK1,k2_zfmisc_1(sK2,sK3))
      & v1_finset_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

fof(f19,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4(sK1,sK3,sK2),sK5(sK1,sK3,sK2))) ),
    inference(unit_resulting_resolution,[],[f49,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f65,plain,(
    ~ r1_tarski(sK1,k2_zfmisc_1(sK4(sK1,sK3,sK2),sK3)) ),
    inference(global_subsumption,[],[f56,f64])).

fof(f64,plain,
    ( ~ r1_tarski(sK4(sK1,sK3,sK2),sK2)
    | ~ r1_tarski(sK1,k2_zfmisc_1(sK4(sK1,sK3,sK2),sK3)) ),
    inference(resolution,[],[f54,f21])).

fof(f21,plain,(
    ! [X3] :
      ( ~ v1_finset_1(X3)
      | ~ r1_tarski(X3,sK2)
      | ~ r1_tarski(sK1,k2_zfmisc_1(X3,sK3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    v1_finset_1(sK4(sK1,sK3,sK2)) ),
    inference(unit_resulting_resolution,[],[f49,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v1_finset_1(sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    r1_tarski(sK4(sK1,sK3,sK2),sK2) ),
    inference(resolution,[],[f49,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tarski(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:44:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (3876)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.20/0.47  % (3878)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.48  % (3895)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.48  % (3895)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f65,f59,f68,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,sK5(sK1,sK3,sK2)),k2_zfmisc_1(X0,sK3))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f51,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    r1_tarski(sK5(sK1,sK3,sK2),sK3)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f49,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tarski(sK5(X0,X1,X2),X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2))) & r1_tarski(sK5(X0,X1,X2),X1) & v1_finset_1(sK5(X0,X1,X2)) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2))) | ~sP0(X0,X1,X2))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f16,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X1) & v1_finset_1(X4) & r1_tarski(X3,X2) & v1_finset_1(X3)) => (r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2))) & r1_tarski(sK5(X0,X1,X2),X1) & v1_finset_1(sK5(X0,X1,X2)) & r1_tarski(sK4(X0,X1,X2),X2) & v1_finset_1(sK4(X0,X1,X2))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X1) & v1_finset_1(X4) & r1_tarski(X3,X2) & v1_finset_1(X3)) | ~sP0(X0,X1,X2))),
% 0.20/0.48    inference(rectify,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X2,X1] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~sP0(X0,X2,X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X2,X1] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~sP0(X0,X2,X1))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    sP0(sK1,sK3,sK2)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f19,f20,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_finset_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | sP0(X0,X2,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (sP0(X0,X2,X1) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.20/0.48    inference(definition_folding,[],[f10,f11])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    r1_tarski(sK1,k2_zfmisc_1(sK2,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X3] : (~r1_tarski(sK1,k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X3,sK2) | ~v1_finset_1(X3)) & r1_tarski(sK1,k2_zfmisc_1(sK2,sK3)) & v1_finset_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f6,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0)) => (! [X3] : (~r1_tarski(sK1,k2_zfmisc_1(X3,sK3)) | ~r1_tarski(X3,sK2) | ~v1_finset_1(X3)) & r1_tarski(sK1,k2_zfmisc_1(sK2,sK3)) & v1_finset_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    v1_finset_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    r1_tarski(sK1,k2_zfmisc_1(sK4(sK1,sK3,sK2),sK5(sK1,sK3,sK2)))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f49,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tarski(X0,k2_zfmisc_1(sK4(X0,X1,X2),sK5(X0,X1,X2)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ~r1_tarski(sK1,k2_zfmisc_1(sK4(sK1,sK3,sK2),sK3))),
% 0.20/0.48    inference(global_subsumption,[],[f56,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ~r1_tarski(sK4(sK1,sK3,sK2),sK2) | ~r1_tarski(sK1,k2_zfmisc_1(sK4(sK1,sK3,sK2),sK3))),
% 0.20/0.48    inference(resolution,[],[f54,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X3] : (~v1_finset_1(X3) | ~r1_tarski(X3,sK2) | ~r1_tarski(sK1,k2_zfmisc_1(X3,sK3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    v1_finset_1(sK4(sK1,sK3,sK2))),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f49,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v1_finset_1(sK4(X0,X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    r1_tarski(sK4(sK1,sK3,sK2),sK2)),
% 0.20/0.48    inference(resolution,[],[f49,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tarski(sK4(X0,X1,X2),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (3895)------------------------------
% 0.20/0.48  % (3895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3895)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (3895)Memory used [KB]: 5373
% 0.20/0.48  % (3895)Time elapsed: 0.058 s
% 0.20/0.48  % (3895)------------------------------
% 0.20/0.48  % (3895)------------------------------
% 0.20/0.48  % (3873)Success in time 0.115 s
%------------------------------------------------------------------------------
