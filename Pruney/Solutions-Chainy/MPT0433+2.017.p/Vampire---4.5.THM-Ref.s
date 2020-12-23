%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:53 EST 2020

% Result     : Theorem 3.77s
% Output     : Refutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 153 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   21
%              Number of atoms          :  164 ( 409 expanded)
%              Number of equality atoms :   16 (  60 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4844,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f120,f4843])).

fof(f4843,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f4842])).

fof(f4842,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f4837,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4837,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl2_2 ),
    inference(resolution,[],[f4835,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4835,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK1,X0) )
    | spl2_2 ),
    inference(superposition,[],[f4827,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f4827,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK1,X0),sK1)
    | spl2_2 ),
    inference(resolution,[],[f4825,f57])).

fof(f4825,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(k2_xboole_0(X0,X1),sK1) )
    | spl2_2 ),
    inference(superposition,[],[f4795,f52])).

fof(f4795,plain,
    ( ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_xboole_0(sK1,X0),X1),sK1)
    | spl2_2 ),
    inference(resolution,[],[f874,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f874,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X5),X3)
        | ~ r1_tarski(k2_xboole_0(X3,X4),sK1) )
    | spl2_2 ),
    inference(resolution,[],[f708,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f708,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_xboole_0(sK0,sK1),X0)
        | ~ r1_tarski(k2_xboole_0(X0,X1),sK1) )
    | spl2_2 ),
    inference(resolution,[],[f702,f53])).

fof(f702,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k3_xboole_0(sK0,sK1),X0) )
    | spl2_2 ),
    inference(superposition,[],[f698,f52])).

fof(f698,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),sK1)
    | spl2_2 ),
    inference(resolution,[],[f697,f53])).

fof(f697,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f696,f57])).

fof(f696,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | spl2_2 ),
    inference(superposition,[],[f674,f52])).

fof(f674,plain,
    ( ~ r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),k1_relat_1(sK1))
    | spl2_2 ),
    inference(superposition,[],[f132,f171])).

fof(f171,plain,(
    ! [X0] : k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK1)) ),
    inference(resolution,[],[f61,f58])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k3_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f61,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X1,sK1)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f132,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k1_relat_1(sK1))
    | spl2_2 ),
    inference(resolution,[],[f84,f53])).

fof(f84,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f120,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f110,f57])).

fof(f110,plain,
    ( ! [X1] : ~ r1_tarski(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,X1))
    | spl2_1 ),
    inference(resolution,[],[f108,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f108,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f107,f57])).

fof(f107,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_1 ),
    inference(superposition,[],[f98,f52])).

fof(f98,plain,
    ( ~ r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)),k1_relat_1(sK0))
    | spl2_1 ),
    inference(subsumption_resolution,[],[f96,f58])).

fof(f96,plain,
    ( ~ r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)),k1_relat_1(sK0))
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(superposition,[],[f86,f59])).

fof(f59,plain,(
    ! [X1] :
      ( k1_relat_1(k2_xboole_0(X1,sK0)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f40,f43])).

fof(f86,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k1_relat_1(sK0))
    | spl2_1 ),
    inference(resolution,[],[f80,f53])).

fof(f80,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f85,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f74,f82,f78])).

fof(f74,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f42,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (717)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.48  % (734)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (733)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (716)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (713)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.55  % (714)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.55  % (724)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.55  % (711)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (715)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.56  % (710)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.56  % (729)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.56  % (712)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.56  % (727)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.56  % (730)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.57  % (720)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.57  % (718)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.57  % (719)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.58  % (725)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.58  % (732)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.58  % (726)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.58  % (721)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.58  % (722)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.59  % (737)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.59  % (723)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.60  % (728)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.60  % (735)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 3.15/0.80  % (719)Refutation not found, incomplete strategy% (719)------------------------------
% 3.15/0.80  % (719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.80  % (719)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.80  
% 3.15/0.80  % (719)Memory used [KB]: 6140
% 3.15/0.80  % (719)Time elapsed: 0.365 s
% 3.15/0.80  % (719)------------------------------
% 3.15/0.80  % (719)------------------------------
% 3.77/0.85  % (716)Refutation found. Thanks to Tanya!
% 3.77/0.85  % SZS status Theorem for theBenchmark
% 3.77/0.85  % SZS output start Proof for theBenchmark
% 3.77/0.85  fof(f4844,plain,(
% 3.77/0.85    $false),
% 3.77/0.85    inference(avatar_sat_refutation,[],[f85,f120,f4843])).
% 3.77/0.85  fof(f4843,plain,(
% 3.77/0.85    spl2_2),
% 3.77/0.85    inference(avatar_contradiction_clause,[],[f4842])).
% 3.77/0.85  fof(f4842,plain,(
% 3.77/0.85    $false | spl2_2),
% 3.77/0.85    inference(subsumption_resolution,[],[f4837,f57])).
% 3.77/0.85  fof(f57,plain,(
% 3.77/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.77/0.85    inference(equality_resolution,[],[f49])).
% 3.77/0.85  fof(f49,plain,(
% 3.77/0.85    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.77/0.85    inference(cnf_transformation,[],[f39])).
% 3.77/0.85  fof(f39,plain,(
% 3.77/0.85    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.85    inference(flattening,[],[f38])).
% 3.77/0.85  fof(f38,plain,(
% 3.77/0.85    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.85    inference(nnf_transformation,[],[f1])).
% 3.77/0.85  fof(f1,axiom,(
% 3.77/0.85    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.77/0.85  fof(f4837,plain,(
% 3.77/0.85    ~r1_tarski(sK1,sK1) | spl2_2),
% 3.77/0.85    inference(resolution,[],[f4835,f56])).
% 3.77/0.85  fof(f56,plain,(
% 3.77/0.85    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.77/0.85    inference(equality_resolution,[],[f50])).
% 3.77/0.85  fof(f50,plain,(
% 3.77/0.85    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.77/0.85    inference(cnf_transformation,[],[f39])).
% 3.77/0.85  fof(f4835,plain,(
% 3.77/0.85    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(sK1,X0)) ) | spl2_2),
% 3.77/0.85    inference(superposition,[],[f4827,f52])).
% 3.77/0.85  fof(f52,plain,(
% 3.77/0.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.77/0.85    inference(cnf_transformation,[],[f32])).
% 3.77/0.85  fof(f32,plain,(
% 3.77/0.85    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.77/0.85    inference(ennf_transformation,[],[f5])).
% 3.77/0.85  fof(f5,axiom,(
% 3.77/0.85    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.77/0.85  fof(f4827,plain,(
% 3.77/0.85    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK1,X0),sK1)) ) | spl2_2),
% 3.77/0.85    inference(resolution,[],[f4825,f57])).
% 3.77/0.85  fof(f4825,plain,(
% 3.77/0.85    ( ! [X0,X1] : (~r1_tarski(sK1,X0) | ~r1_tarski(k2_xboole_0(X0,X1),sK1)) ) | spl2_2),
% 3.77/0.85    inference(superposition,[],[f4795,f52])).
% 3.77/0.85  fof(f4795,plain,(
% 3.77/0.85    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_xboole_0(sK1,X0),X1),sK1)) ) | spl2_2),
% 3.77/0.85    inference(resolution,[],[f874,f46])).
% 3.77/0.85  fof(f46,plain,(
% 3.77/0.85    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 3.77/0.85    inference(cnf_transformation,[],[f10])).
% 3.77/0.85  fof(f10,axiom,(
% 3.77/0.85    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 3.77/0.85  fof(f874,plain,(
% 3.77/0.85    ( ! [X4,X5,X3] : (~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X5),X3) | ~r1_tarski(k2_xboole_0(X3,X4),sK1)) ) | spl2_2),
% 3.77/0.85    inference(resolution,[],[f708,f53])).
% 3.77/0.85  fof(f53,plain,(
% 3.77/0.85    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 3.77/0.85    inference(cnf_transformation,[],[f33])).
% 3.77/0.85  fof(f33,plain,(
% 3.77/0.85    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 3.77/0.85    inference(ennf_transformation,[],[f4])).
% 3.77/0.85  fof(f4,axiom,(
% 3.77/0.85    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 3.77/0.85  fof(f708,plain,(
% 3.77/0.85    ( ! [X0,X1] : (~r1_tarski(k3_xboole_0(sK0,sK1),X0) | ~r1_tarski(k2_xboole_0(X0,X1),sK1)) ) | spl2_2),
% 3.77/0.85    inference(resolution,[],[f702,f53])).
% 3.77/0.85  fof(f702,plain,(
% 3.77/0.85    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r1_tarski(k3_xboole_0(sK0,sK1),X0)) ) | spl2_2),
% 3.77/0.85    inference(superposition,[],[f698,f52])).
% 3.77/0.85  fof(f698,plain,(
% 3.77/0.85    ( ! [X0] : (~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),X0),sK1)) ) | spl2_2),
% 3.77/0.85    inference(resolution,[],[f697,f53])).
% 3.77/0.85  fof(f697,plain,(
% 3.77/0.85    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_2),
% 3.77/0.85    inference(subsumption_resolution,[],[f696,f57])).
% 3.77/0.85  fof(f696,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(sK1),k1_relat_1(sK1)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | spl2_2),
% 3.77/0.85    inference(superposition,[],[f674,f52])).
% 3.77/0.85  fof(f674,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),k1_relat_1(sK1)) | spl2_2),
% 3.77/0.85    inference(superposition,[],[f132,f171])).
% 3.77/0.85  fof(f171,plain,(
% 3.77/0.85    ( ! [X0] : (k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,X0),sK1)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X0)),k1_relat_1(sK1))) )),
% 3.77/0.85    inference(resolution,[],[f61,f58])).
% 3.77/0.85  fof(f58,plain,(
% 3.77/0.85    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK0,X0))) )),
% 3.77/0.85    inference(resolution,[],[f40,f48])).
% 3.77/0.85  fof(f48,plain,(
% 3.77/0.85    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 3.77/0.85    inference(cnf_transformation,[],[f31])).
% 3.77/0.85  fof(f31,plain,(
% 3.77/0.85    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.77/0.85    inference(ennf_transformation,[],[f21])).
% 3.77/0.85  fof(f21,axiom,(
% 3.77/0.85    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 3.77/0.85  fof(f40,plain,(
% 3.77/0.85    v1_relat_1(sK0)),
% 3.77/0.85    inference(cnf_transformation,[],[f37])).
% 3.77/0.85  fof(f37,plain,(
% 3.77/0.85    (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 3.77/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f36,f35])).
% 3.77/0.85  fof(f35,plain,(
% 3.77/0.85    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 3.77/0.85    introduced(choice_axiom,[])).
% 3.77/0.85  fof(f36,plain,(
% 3.77/0.85    ? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 3.77/0.85    introduced(choice_axiom,[])).
% 3.77/0.85  fof(f25,plain,(
% 3.77/0.85    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 3.77/0.85    inference(ennf_transformation,[],[f24])).
% 3.77/0.85  fof(f24,negated_conjecture,(
% 3.77/0.85    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 3.77/0.85    inference(negated_conjecture,[],[f23])).
% 3.77/0.85  fof(f23,conjecture,(
% 3.77/0.85    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).
% 3.77/0.85  fof(f61,plain,(
% 3.77/0.85    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X1,sK1)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK1))) )),
% 3.77/0.85    inference(resolution,[],[f41,f43])).
% 3.77/0.85  fof(f43,plain,(
% 3.77/0.85    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 3.77/0.85    inference(cnf_transformation,[],[f26])).
% 3.77/0.85  fof(f26,plain,(
% 3.77/0.85    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.77/0.85    inference(ennf_transformation,[],[f22])).
% 3.77/0.85  fof(f22,axiom,(
% 3.77/0.85    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 3.77/0.85  fof(f41,plain,(
% 3.77/0.85    v1_relat_1(sK1)),
% 3.77/0.85    inference(cnf_transformation,[],[f37])).
% 3.77/0.85  fof(f132,plain,(
% 3.77/0.85    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k1_relat_1(sK1))) ) | spl2_2),
% 3.77/0.85    inference(resolution,[],[f84,f53])).
% 3.77/0.85  fof(f84,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | spl2_2),
% 3.77/0.85    inference(avatar_component_clause,[],[f82])).
% 3.77/0.85  fof(f82,plain,(
% 3.77/0.85    spl2_2 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1))),
% 3.77/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.77/0.85  fof(f120,plain,(
% 3.77/0.85    spl2_1),
% 3.77/0.85    inference(avatar_contradiction_clause,[],[f115])).
% 3.77/0.85  fof(f115,plain,(
% 3.77/0.85    $false | spl2_1),
% 3.77/0.85    inference(resolution,[],[f110,f57])).
% 3.77/0.85  fof(f110,plain,(
% 3.77/0.85    ( ! [X1] : (~r1_tarski(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,X1))) ) | spl2_1),
% 3.77/0.85    inference(resolution,[],[f108,f45])).
% 3.77/0.85  fof(f45,plain,(
% 3.77/0.85    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 3.77/0.85    inference(cnf_transformation,[],[f29])).
% 3.77/0.85  fof(f29,plain,(
% 3.77/0.85    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.77/0.85    inference(ennf_transformation,[],[f6])).
% 3.77/0.85  fof(f6,axiom,(
% 3.77/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 3.77/0.85  fof(f108,plain,(
% 3.77/0.85    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_1),
% 3.77/0.85    inference(subsumption_resolution,[],[f107,f57])).
% 3.77/0.85  fof(f107,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_1),
% 3.77/0.85    inference(superposition,[],[f98,f52])).
% 3.77/0.85  fof(f98,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)),k1_relat_1(sK0)) | spl2_1),
% 3.77/0.85    inference(subsumption_resolution,[],[f96,f58])).
% 3.77/0.85  fof(f96,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(k2_xboole_0(k3_xboole_0(sK0,sK1),sK0)),k1_relat_1(sK0)) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 3.77/0.85    inference(superposition,[],[f86,f59])).
% 3.77/0.85  fof(f59,plain,(
% 3.77/0.85    ( ! [X1] : (k1_relat_1(k2_xboole_0(X1,sK0)) = k2_xboole_0(k1_relat_1(X1),k1_relat_1(sK0)) | ~v1_relat_1(X1)) )),
% 3.77/0.85    inference(resolution,[],[f40,f43])).
% 3.77/0.85  fof(f86,plain,(
% 3.77/0.85    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,sK1)),X0),k1_relat_1(sK0))) ) | spl2_1),
% 3.77/0.85    inference(resolution,[],[f80,f53])).
% 3.77/0.85  fof(f80,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0)) | spl2_1),
% 3.77/0.85    inference(avatar_component_clause,[],[f78])).
% 3.77/0.85  fof(f78,plain,(
% 3.77/0.85    spl2_1 <=> r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 3.77/0.85    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.77/0.85  fof(f85,plain,(
% 3.77/0.85    ~spl2_1 | ~spl2_2),
% 3.77/0.85    inference(avatar_split_clause,[],[f74,f82,f78])).
% 3.77/0.85  fof(f74,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k1_relat_1(sK0))),
% 3.77/0.85    inference(resolution,[],[f42,f44])).
% 3.77/0.85  fof(f44,plain,(
% 3.77/0.85    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.77/0.85    inference(cnf_transformation,[],[f28])).
% 3.77/0.85  fof(f28,plain,(
% 3.77/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 3.77/0.85    inference(flattening,[],[f27])).
% 3.77/0.85  fof(f27,plain,(
% 3.77/0.85    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.77/0.85    inference(ennf_transformation,[],[f7])).
% 3.77/0.85  fof(f7,axiom,(
% 3.77/0.85    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 3.77/0.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 3.77/0.85  fof(f42,plain,(
% 3.77/0.85    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 3.77/0.85    inference(cnf_transformation,[],[f37])).
% 3.77/0.85  % SZS output end Proof for theBenchmark
% 3.77/0.85  % (716)------------------------------
% 3.77/0.85  % (716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.85  % (716)Termination reason: Refutation
% 3.77/0.85  
% 3.77/0.85  % (716)Memory used [KB]: 13688
% 3.77/0.85  % (716)Time elapsed: 0.350 s
% 3.77/0.85  % (716)------------------------------
% 3.77/0.85  % (716)------------------------------
% 3.77/0.85  % (709)Success in time 0.49 s
%------------------------------------------------------------------------------
