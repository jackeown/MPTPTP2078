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
% DateTime   : Thu Dec  3 12:53:54 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 144 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  188 ( 379 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f702,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f623,f632,f637,f701])).

fof(f701,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f700])).

fof(f700,plain,
    ( $false
    | spl2_9 ),
    inference(subsumption_resolution,[],[f699,f43])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f699,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_9 ),
    inference(subsumption_resolution,[],[f698,f44])).

fof(f44,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f698,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl2_9 ),
    inference(superposition,[],[f696,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f696,plain,
    ( ! [X0] : ~ r1_tarski(sK0,k10_relat_1(sK1,X0))
    | spl2_9 ),
    inference(subsumption_resolution,[],[f694,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f694,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,sK0)
        | ~ r1_tarski(sK0,k10_relat_1(sK1,X0)) )
    | spl2_9 ),
    inference(superposition,[],[f680,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f680,plain,
    ( ! [X4] : ~ r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X4)))
    | spl2_9 ),
    inference(subsumption_resolution,[],[f675,f43])).

fof(f675,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X4)))
        | ~ v1_relat_1(sK1) )
    | spl2_9 ),
    inference(resolution,[],[f652,f246])).

fof(f246,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9)))
      | ~ v1_relat_1(X8) ) ),
    inference(subsumption_resolution,[],[f240,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f240,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9)))
      | ~ v1_relat_1(k7_relat_1(X8,X9))
      | ~ v1_relat_1(X8) ) ),
    inference(superposition,[],[f50,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f652,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,sK0)))
        | ~ r1_tarski(sK0,X0) )
    | spl2_9 ),
    inference(resolution,[],[f622,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f62,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f622,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f620])).

fof(f620,plain,
    ( spl2_9
  <=> r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f637,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | spl2_8 ),
    inference(subsumption_resolution,[],[f633,f43])).

fof(f633,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_8 ),
    inference(resolution,[],[f618,f48])).

fof(f618,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl2_8
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f632,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | spl2_7 ),
    inference(subsumption_resolution,[],[f628,f43])).

fof(f628,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_7 ),
    inference(resolution,[],[f614,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f614,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f612])).

fof(f612,plain,
    ( spl2_7
  <=> r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f623,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f610,f620,f616,f612])).

fof(f610,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    inference(subsumption_resolution,[],[f597,f43])).

fof(f597,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ r1_tarski(k7_relat_1(sK1,sK0),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f295,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f46,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f295,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK0,k10_relat_1(X2,k9_relat_1(sK1,sK0)))
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X2,sK1) ) ),
    inference(subsumption_resolution,[],[f286,f43])).

fof(f286,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(sK0,k10_relat_1(X2,k9_relat_1(sK1,sK0))) ) ),
    inference(resolution,[],[f53,f99])).

fof(f99,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      | ~ r1_tarski(sK0,X8) ) ),
    inference(resolution,[],[f71,f45])).

fof(f45,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:18:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (25865)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (25869)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (25866)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (25878)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (25882)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (25871)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (25864)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (25883)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (25872)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (25874)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (25875)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (25873)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.26/0.52  % (25861)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.26/0.52  % (25870)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.26/0.52  % (25867)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.26/0.52  % (25881)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.26/0.52  % (25863)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.26/0.52  % (25880)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.26/0.53  % (25868)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.26/0.53  % (25879)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.26/0.53  % (25860)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.26/0.54  % (25877)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.36/0.54  % (25862)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.36/0.54  % (25876)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.36/0.55  % (25884)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.36/0.55  % (25885)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.36/0.57  % (25864)Refutation found. Thanks to Tanya!
% 1.36/0.57  % SZS status Theorem for theBenchmark
% 1.36/0.57  % SZS output start Proof for theBenchmark
% 1.36/0.57  fof(f702,plain,(
% 1.36/0.57    $false),
% 1.36/0.57    inference(avatar_sat_refutation,[],[f623,f632,f637,f701])).
% 1.36/0.57  fof(f701,plain,(
% 1.36/0.57    spl2_9),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f700])).
% 1.36/0.57  fof(f700,plain,(
% 1.36/0.57    $false | spl2_9),
% 1.36/0.57    inference(subsumption_resolution,[],[f699,f43])).
% 1.36/0.57  fof(f43,plain,(
% 1.36/0.57    v1_relat_1(sK1)),
% 1.36/0.57    inference(cnf_transformation,[],[f40])).
% 1.36/0.57  fof(f40,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 1.36/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f39])).
% 1.36/0.57  fof(f39,plain,(
% 1.36/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 1.36/0.57    introduced(choice_axiom,[])).
% 1.36/0.57  fof(f20,plain,(
% 1.36/0.57    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 1.36/0.57    inference(flattening,[],[f19])).
% 1.36/0.57  fof(f19,plain,(
% 1.36/0.57    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f18])).
% 1.36/0.57  fof(f18,negated_conjecture,(
% 1.36/0.57    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.36/0.57    inference(negated_conjecture,[],[f17])).
% 1.36/0.57  fof(f17,conjecture,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.36/0.57  fof(f699,plain,(
% 1.36/0.57    ~v1_relat_1(sK1) | spl2_9),
% 1.36/0.57    inference(subsumption_resolution,[],[f698,f44])).
% 1.36/0.57  fof(f44,plain,(
% 1.36/0.57    r1_tarski(sK0,k1_relat_1(sK1))),
% 1.36/0.57    inference(cnf_transformation,[],[f40])).
% 1.36/0.57  fof(f698,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | spl2_9),
% 1.36/0.57    inference(superposition,[],[f696,f46])).
% 1.36/0.57  fof(f46,plain,(
% 1.36/0.57    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f21])).
% 1.36/0.57  fof(f21,plain,(
% 1.36/0.57    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f11])).
% 1.36/0.57  fof(f11,axiom,(
% 1.36/0.57    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.36/0.57  fof(f696,plain,(
% 1.36/0.57    ( ! [X0] : (~r1_tarski(sK0,k10_relat_1(sK1,X0))) ) | spl2_9),
% 1.36/0.57    inference(subsumption_resolution,[],[f694,f64])).
% 1.36/0.57  fof(f64,plain,(
% 1.36/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.57    inference(equality_resolution,[],[f57])).
% 1.36/0.57  fof(f57,plain,(
% 1.36/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.36/0.57    inference(cnf_transformation,[],[f42])).
% 1.36/0.57  fof(f42,plain,(
% 1.36/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.57    inference(flattening,[],[f41])).
% 1.36/0.57  fof(f41,plain,(
% 1.36/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.57    inference(nnf_transformation,[],[f1])).
% 1.36/0.57  fof(f1,axiom,(
% 1.36/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.57  fof(f694,plain,(
% 1.36/0.57    ( ! [X0] : (~r1_tarski(sK0,sK0) | ~r1_tarski(sK0,k10_relat_1(sK1,X0))) ) | spl2_9),
% 1.36/0.57    inference(superposition,[],[f680,f54])).
% 1.36/0.57  fof(f54,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f30])).
% 1.36/0.57  fof(f30,plain,(
% 1.36/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f5])).
% 1.36/0.57  fof(f5,axiom,(
% 1.36/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.36/0.57  fof(f680,plain,(
% 1.36/0.57    ( ! [X4] : (~r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X4)))) ) | spl2_9),
% 1.36/0.57    inference(subsumption_resolution,[],[f675,f43])).
% 1.36/0.57  fof(f675,plain,(
% 1.36/0.57    ( ! [X4] : (~r1_tarski(sK0,k3_xboole_0(sK0,k10_relat_1(sK1,X4))) | ~v1_relat_1(sK1)) ) | spl2_9),
% 1.36/0.57    inference(resolution,[],[f652,f246])).
% 1.36/0.57  fof(f246,plain,(
% 1.36/0.57    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9))) | ~v1_relat_1(X8)) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f240,f48])).
% 1.36/0.57  fof(f48,plain,(
% 1.36/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f22])).
% 1.36/0.57  fof(f22,plain,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.36/0.57    inference(ennf_transformation,[],[f8])).
% 1.36/0.57  fof(f8,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.36/0.57  fof(f240,plain,(
% 1.36/0.57    ( ! [X10,X8,X9] : (r1_tarski(k3_xboole_0(X9,k10_relat_1(X8,X10)),k1_relat_1(k7_relat_1(X8,X9))) | ~v1_relat_1(k7_relat_1(X8,X9)) | ~v1_relat_1(X8)) )),
% 1.36/0.57    inference(superposition,[],[f50,f59])).
% 1.36/0.57  fof(f59,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f32])).
% 1.36/0.57  fof(f32,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.36/0.57    inference(ennf_transformation,[],[f16])).
% 1.36/0.57  fof(f16,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.36/0.57  fof(f50,plain,(
% 1.36/0.57    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f24])).
% 1.36/0.57  fof(f24,plain,(
% 1.36/0.57    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f10])).
% 1.36/0.57  fof(f10,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.36/0.57  fof(f652,plain,(
% 1.36/0.57    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~r1_tarski(sK0,X0)) ) | spl2_9),
% 1.36/0.57    inference(resolution,[],[f622,f71])).
% 1.36/0.57  fof(f71,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.36/0.57    inference(superposition,[],[f62,f55])).
% 1.36/0.57  fof(f55,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f31])).
% 1.36/0.57  fof(f31,plain,(
% 1.36/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f4])).
% 1.36/0.57  fof(f4,axiom,(
% 1.36/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.36/0.57  fof(f62,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f36])).
% 1.36/0.57  fof(f36,plain,(
% 1.36/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.36/0.57    inference(ennf_transformation,[],[f3])).
% 1.36/0.57  fof(f3,axiom,(
% 1.36/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.36/0.57  fof(f622,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | spl2_9),
% 1.36/0.57    inference(avatar_component_clause,[],[f620])).
% 1.36/0.57  fof(f620,plain,(
% 1.36/0.57    spl2_9 <=> r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0)))),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.36/0.57  fof(f637,plain,(
% 1.36/0.57    spl2_8),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f636])).
% 1.36/0.57  fof(f636,plain,(
% 1.36/0.57    $false | spl2_8),
% 1.36/0.57    inference(subsumption_resolution,[],[f633,f43])).
% 1.36/0.57  fof(f633,plain,(
% 1.36/0.57    ~v1_relat_1(sK1) | spl2_8),
% 1.36/0.57    inference(resolution,[],[f618,f48])).
% 1.36/0.57  fof(f618,plain,(
% 1.36/0.57    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_8),
% 1.36/0.57    inference(avatar_component_clause,[],[f616])).
% 1.36/0.57  fof(f616,plain,(
% 1.36/0.57    spl2_8 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.36/0.57  fof(f632,plain,(
% 1.36/0.57    spl2_7),
% 1.36/0.57    inference(avatar_contradiction_clause,[],[f631])).
% 1.36/0.57  fof(f631,plain,(
% 1.36/0.57    $false | spl2_7),
% 1.36/0.57    inference(subsumption_resolution,[],[f628,f43])).
% 1.36/0.57  fof(f628,plain,(
% 1.36/0.57    ~v1_relat_1(sK1) | spl2_7),
% 1.36/0.57    inference(resolution,[],[f614,f49])).
% 1.36/0.57  fof(f49,plain,(
% 1.36/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f23])).
% 1.36/0.57  fof(f23,plain,(
% 1.36/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f14])).
% 1.36/0.57  fof(f14,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 1.36/0.57  fof(f614,plain,(
% 1.36/0.57    ~r1_tarski(k7_relat_1(sK1,sK0),sK1) | spl2_7),
% 1.36/0.57    inference(avatar_component_clause,[],[f612])).
% 1.36/0.57  fof(f612,plain,(
% 1.36/0.57    spl2_7 <=> r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 1.36/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.36/0.57  fof(f623,plain,(
% 1.36/0.57    ~spl2_7 | ~spl2_8 | ~spl2_9),
% 1.36/0.57    inference(avatar_split_clause,[],[f610,f620,f616,f612])).
% 1.36/0.57  fof(f610,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 1.36/0.57    inference(subsumption_resolution,[],[f597,f43])).
% 1.36/0.57  fof(f597,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~r1_tarski(k7_relat_1(sK1,sK0),sK1) | ~v1_relat_1(sK1)),
% 1.36/0.57    inference(superposition,[],[f295,f112])).
% 1.36/0.57  fof(f112,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f111,f48])).
% 1.36/0.57  fof(f111,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X0,X1)) = k10_relat_1(k7_relat_1(X0,X1),k9_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.36/0.57    inference(superposition,[],[f46,f51])).
% 1.36/0.57  fof(f51,plain,(
% 1.36/0.57    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f25])).
% 1.36/0.57  fof(f25,plain,(
% 1.36/0.57    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f9])).
% 1.36/0.57  fof(f9,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.36/0.57  fof(f295,plain,(
% 1.36/0.57    ( ! [X2] : (~r1_tarski(sK0,k10_relat_1(X2,k9_relat_1(sK1,sK0))) | ~v1_relat_1(X2) | ~r1_tarski(X2,sK1)) )),
% 1.36/0.57    inference(subsumption_resolution,[],[f286,f43])).
% 1.36/0.57  fof(f286,plain,(
% 1.36/0.57    ( ! [X2] : (~r1_tarski(X2,sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(X2) | ~r1_tarski(sK0,k10_relat_1(X2,k9_relat_1(sK1,sK0)))) )),
% 1.36/0.57    inference(resolution,[],[f53,f99])).
% 1.36/0.57  fof(f99,plain,(
% 1.36/0.57    ( ! [X8] : (~r1_tarski(X8,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) | ~r1_tarski(sK0,X8)) )),
% 1.36/0.57    inference(resolution,[],[f71,f45])).
% 1.36/0.57  fof(f45,plain,(
% 1.36/0.57    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 1.36/0.57    inference(cnf_transformation,[],[f40])).
% 1.36/0.57  fof(f53,plain,(
% 1.36/0.57    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.36/0.57    inference(cnf_transformation,[],[f29])).
% 1.36/0.57  fof(f29,plain,(
% 1.36/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(flattening,[],[f28])).
% 1.36/0.57  fof(f28,plain,(
% 1.36/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.36/0.57    inference(ennf_transformation,[],[f13])).
% 1.36/0.57  fof(f13,axiom,(
% 1.36/0.57    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 1.36/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).
% 1.36/0.57  % SZS output end Proof for theBenchmark
% 1.36/0.57  % (25864)------------------------------
% 1.36/0.57  % (25864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (25864)Termination reason: Refutation
% 1.36/0.57  
% 1.36/0.57  % (25864)Memory used [KB]: 6396
% 1.36/0.57  % (25864)Time elapsed: 0.122 s
% 1.36/0.57  % (25864)------------------------------
% 1.36/0.57  % (25864)------------------------------
% 1.36/0.59  % (25859)Success in time 0.23 s
%------------------------------------------------------------------------------
