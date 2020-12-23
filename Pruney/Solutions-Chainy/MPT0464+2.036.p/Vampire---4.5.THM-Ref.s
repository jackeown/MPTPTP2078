%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:30 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 ( 378 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f162,f165,f190])).

% (6809)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f190,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f187,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f187,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f182,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X2,X0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f84,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f84,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(resolution,[],[f43,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f182,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f181,f156])).

fof(f156,plain,
    ( v1_relat_1(k3_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl3_3
  <=> v1_relat_1(k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f181,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f180,f32])).

fof(f32,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f180,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f178,f30])).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f178,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK2)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(resolution,[],[f131,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

fof(f131,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_2
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f165,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f163,f31])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f163,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_3 ),
    inference(resolution,[],[f157,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f157,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f155])).

fof(f162,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f152,f125,f155])).

fof(f125,plain,
    ( spl3_1
  <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f152,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f151,f31])).

fof(f151,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f150,f30])).

fof(f150,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f147,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f147,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(resolution,[],[f34,f127])).

fof(f127,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f132,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f111,f129,f125])).

fof(f111,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:50:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (6801)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (6795)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (6816)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (6793)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (6800)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (6812)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (6803)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (6796)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (6807)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (6814)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (6798)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (6815)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (6806)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.31/0.53  % (6804)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.31/0.53  % (6796)Refutation found. Thanks to Tanya!
% 1.31/0.53  % SZS status Theorem for theBenchmark
% 1.31/0.53  % SZS output start Proof for theBenchmark
% 1.31/0.53  fof(f191,plain,(
% 1.31/0.53    $false),
% 1.31/0.53    inference(avatar_sat_refutation,[],[f132,f162,f165,f190])).
% 1.31/0.53  % (6809)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.31/0.53  fof(f190,plain,(
% 1.31/0.53    spl3_2 | ~spl3_3),
% 1.31/0.53    inference(avatar_contradiction_clause,[],[f189])).
% 1.31/0.53  fof(f189,plain,(
% 1.31/0.53    $false | (spl3_2 | ~spl3_3)),
% 1.31/0.53    inference(subsumption_resolution,[],[f187,f47])).
% 1.31/0.53  fof(f47,plain,(
% 1.31/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.53    inference(equality_resolution,[],[f41])).
% 1.31/0.53  fof(f41,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.53    inference(cnf_transformation,[],[f29])).
% 1.31/0.53  fof(f29,plain,(
% 1.31/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.53    inference(flattening,[],[f28])).
% 1.31/0.53  fof(f28,plain,(
% 1.31/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.31/0.53    inference(nnf_transformation,[],[f1])).
% 1.31/0.53  fof(f1,axiom,(
% 1.31/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.53  fof(f187,plain,(
% 1.31/0.53    ~r1_tarski(sK2,sK2) | (spl3_2 | ~spl3_3)),
% 1.31/0.53    inference(resolution,[],[f182,f88])).
% 1.31/0.53  fof(f88,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X2,X0),X1) | ~r1_tarski(X0,X1)) )),
% 1.31/0.53    inference(superposition,[],[f84,f38])).
% 1.31/0.53  fof(f38,plain,(
% 1.31/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f18])).
% 1.31/0.53  fof(f18,plain,(
% 1.31/0.53    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.31/0.53    inference(ennf_transformation,[],[f8])).
% 1.31/0.53  fof(f8,axiom,(
% 1.31/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.31/0.53  fof(f84,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2))) )),
% 1.31/0.53    inference(resolution,[],[f43,f45])).
% 1.31/0.53  fof(f45,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f21])).
% 1.31/0.53  fof(f21,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.31/0.53    inference(ennf_transformation,[],[f2])).
% 1.31/0.53  fof(f2,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.31/0.53  fof(f43,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 1.31/0.53    inference(cnf_transformation,[],[f5])).
% 1.31/0.53  fof(f5,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 1.31/0.53  fof(f182,plain,(
% 1.31/0.53    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | (spl3_2 | ~spl3_3)),
% 1.31/0.53    inference(subsumption_resolution,[],[f181,f156])).
% 1.31/0.53  fof(f156,plain,(
% 1.31/0.53    v1_relat_1(k3_xboole_0(sK1,sK2)) | ~spl3_3),
% 1.31/0.53    inference(avatar_component_clause,[],[f155])).
% 1.31/0.53  fof(f155,plain,(
% 1.31/0.53    spl3_3 <=> v1_relat_1(k3_xboole_0(sK1,sK2))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.31/0.53  fof(f181,plain,(
% 1.31/0.53    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_2),
% 1.31/0.53    inference(subsumption_resolution,[],[f180,f32])).
% 1.31/0.53  fof(f32,plain,(
% 1.31/0.53    v1_relat_1(sK2)),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f27,plain,(
% 1.31/0.53    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.31/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f26,f25,f24])).
% 1.31/0.53  fof(f24,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f25,plain,(
% 1.31/0.53    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f26,plain,(
% 1.31/0.53    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 1.31/0.53    introduced(choice_axiom,[])).
% 1.31/0.53  fof(f14,plain,(
% 1.31/0.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f13])).
% 1.31/0.53  fof(f13,negated_conjecture,(
% 1.31/0.53    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.31/0.53    inference(negated_conjecture,[],[f12])).
% 1.31/0.53  fof(f12,conjecture,(
% 1.31/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 1.31/0.53  fof(f180,plain,(
% 1.31/0.53    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_2),
% 1.31/0.53    inference(subsumption_resolution,[],[f178,f30])).
% 1.31/0.53  fof(f30,plain,(
% 1.31/0.53    v1_relat_1(sK0)),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f178,plain,(
% 1.31/0.53    ~r1_tarski(k3_xboole_0(sK1,sK2),sK2) | ~v1_relat_1(sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_2),
% 1.31/0.53    inference(resolution,[],[f131,f34])).
% 1.31/0.53  fof(f34,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f16])).
% 1.31/0.53  fof(f16,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(flattening,[],[f15])).
% 1.31/0.53  fof(f15,plain,(
% 1.31/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f11])).
% 1.31/0.53  fof(f11,axiom,(
% 1.31/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).
% 1.31/0.53  fof(f131,plain,(
% 1.31/0.53    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | spl3_2),
% 1.31/0.53    inference(avatar_component_clause,[],[f129])).
% 1.31/0.53  fof(f129,plain,(
% 1.31/0.53    spl3_2 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.31/0.53  fof(f165,plain,(
% 1.31/0.53    spl3_3),
% 1.31/0.53    inference(avatar_contradiction_clause,[],[f164])).
% 1.31/0.53  fof(f164,plain,(
% 1.31/0.53    $false | spl3_3),
% 1.31/0.53    inference(subsumption_resolution,[],[f163,f31])).
% 1.31/0.53  fof(f31,plain,(
% 1.31/0.53    v1_relat_1(sK1)),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f163,plain,(
% 1.31/0.53    ~v1_relat_1(sK1) | spl3_3),
% 1.31/0.53    inference(resolution,[],[f157,f37])).
% 1.31/0.53  fof(f37,plain,(
% 1.31/0.53    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f17])).
% 1.31/0.53  fof(f17,plain,(
% 1.31/0.53    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.31/0.53    inference(ennf_transformation,[],[f10])).
% 1.31/0.53  fof(f10,axiom,(
% 1.31/0.53    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.31/0.53  fof(f157,plain,(
% 1.31/0.53    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_3),
% 1.31/0.53    inference(avatar_component_clause,[],[f155])).
% 1.31/0.53  fof(f162,plain,(
% 1.31/0.53    ~spl3_3 | spl3_1),
% 1.31/0.53    inference(avatar_split_clause,[],[f152,f125,f155])).
% 1.31/0.53  fof(f125,plain,(
% 1.31/0.53    spl3_1 <=> r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 1.31/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.31/0.53  fof(f152,plain,(
% 1.31/0.53    ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_1),
% 1.31/0.53    inference(subsumption_resolution,[],[f151,f31])).
% 1.31/0.53  fof(f151,plain,(
% 1.31/0.53    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_1),
% 1.31/0.53    inference(subsumption_resolution,[],[f150,f30])).
% 1.31/0.53  fof(f150,plain,(
% 1.31/0.53    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_1),
% 1.31/0.53    inference(subsumption_resolution,[],[f147,f36])).
% 1.31/0.53  fof(f36,plain,(
% 1.31/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f3])).
% 1.31/0.53  fof(f3,axiom,(
% 1.31/0.53    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.31/0.53  fof(f147,plain,(
% 1.31/0.53    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,sK2)) | spl3_1),
% 1.31/0.53    inference(resolution,[],[f34,f127])).
% 1.31/0.53  fof(f127,plain,(
% 1.31/0.53    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1)) | spl3_1),
% 1.31/0.53    inference(avatar_component_clause,[],[f125])).
% 1.31/0.53  fof(f132,plain,(
% 1.31/0.53    ~spl3_1 | ~spl3_2),
% 1.31/0.53    inference(avatar_split_clause,[],[f111,f129,f125])).
% 1.31/0.53  fof(f111,plain,(
% 1.31/0.53    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k5_relat_1(sK0,sK1))),
% 1.31/0.53    inference(resolution,[],[f46,f33])).
% 1.31/0.53  fof(f33,plain,(
% 1.31/0.53    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 1.31/0.53    inference(cnf_transformation,[],[f27])).
% 1.31/0.53  fof(f46,plain,(
% 1.31/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.31/0.53    inference(cnf_transformation,[],[f23])).
% 1.31/0.53  fof(f23,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.31/0.53    inference(flattening,[],[f22])).
% 1.31/0.53  fof(f22,plain,(
% 1.31/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.31/0.53    inference(ennf_transformation,[],[f4])).
% 1.31/0.53  fof(f4,axiom,(
% 1.31/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.31/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.31/0.53  % SZS output end Proof for theBenchmark
% 1.31/0.53  % (6796)------------------------------
% 1.31/0.53  % (6796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (6796)Termination reason: Refutation
% 1.31/0.53  
% 1.31/0.53  % (6796)Memory used [KB]: 6268
% 1.31/0.53  % (6796)Time elapsed: 0.104 s
% 1.31/0.53  % (6796)------------------------------
% 1.31/0.53  % (6796)------------------------------
% 1.31/0.53  % (6813)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.31/0.53  % (6799)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.31/0.53  % (6792)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.31/0.54  % (6791)Success in time 0.174 s
%------------------------------------------------------------------------------
