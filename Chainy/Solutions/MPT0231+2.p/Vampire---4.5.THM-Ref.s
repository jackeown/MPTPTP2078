%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0231+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:18 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   21 (  27 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  55 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1389,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f608,f565,f1383,f805])).

fof(f805,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f415])).

fof(f415,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f414])).

fof(f414,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1383,plain,(
    ~ r1_tarski(k1_tarski(sK2),k1_tarski(sK4)) ),
    inference(resolution,[],[f1134,f1074])).

fof(f1074,plain,(
    ~ sQ29_eqProxy(sK2,sK4) ),
    inference(equality_proxy_replacement,[],[f566,f1058])).

fof(f1058,plain,(
    ! [X1,X0] :
      ( sQ29_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ29_eqProxy])])).

fof(f566,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f461])).

fof(f461,plain,
    ( sK2 != sK4
    & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f327,f460])).

% (4073)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% (4084)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% (4077)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
fof(f460,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK2 != sK4
      & r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f327,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f316])).

fof(f316,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f315])).

fof(f315,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f1134,plain,(
    ! [X0,X1] :
      ( sQ29_eqProxy(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(equality_proxy_replacement,[],[f670,f1058])).

fof(f670,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f355])).

fof(f355,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f318])).

fof(f318,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f565,plain,(
    r1_tarski(k2_tarski(sK2,sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f461])).

fof(f608,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f301])).

fof(f301,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
