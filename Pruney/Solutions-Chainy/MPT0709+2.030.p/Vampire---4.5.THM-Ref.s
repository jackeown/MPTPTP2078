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
% DateTime   : Thu Dec  3 12:54:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  97 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  170 ( 345 expanded)
%              Number of equality atoms :   21 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f71,f76,f82,f89])).

fof(f89,plain,
    ( ~ spl2_4
    | spl2_5
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl2_4
    | spl2_5
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f85,f51])).

fof(f51,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_5
  <=> sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f85,plain,
    ( sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(resolution,[],[f81,f46])).

fof(f46,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_4
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_10
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f82,plain,
    ( spl2_10
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f78,f74,f69,f80])).

fof(f69,plain,
    ( spl2_8
  <=> ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f74,plain,
    ( spl2_9
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 )
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f77,f70])).

fof(f70,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
        | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 )
    | ~ spl2_9 ),
    inference(resolution,[],[f75,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f75,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))
        | ~ r1_tarski(X0,k1_relat_1(sK1)) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f55,f29,f74])).

fof(f29,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK1))
        | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) )
    | ~ spl2_1 ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f71,plain,
    ( spl2_8
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f67,f39,f34,f29,f69])).

fof(f34,plain,
    ( spl2_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f39,plain,
    ( spl2_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f66,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f36,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f65,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl2_3 ),
    inference(resolution,[],[f22,f41])).

fof(f41,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f52,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f20,f49])).

fof(f20,plain,(
    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
    & v2_funct_1(sK1)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))
      & v2_funct_1(sK1)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f47,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n010.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 15:44:14 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.50  % (14067)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (14064)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (14078)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (14072)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (14062)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (14084)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (14085)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (14079)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (14066)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (14064)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f71,f76,f82,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~spl2_4 | spl2_5 | ~spl2_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    $false | (~spl2_4 | spl2_5 | ~spl2_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f85,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | spl2_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl2_5 <=> sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    sK0 = k10_relat_1(sK1,k9_relat_1(sK1,sK0)) | (~spl2_4 | ~spl2_10)),
% 0.21/0.52    inference(resolution,[],[f81,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    spl2_4 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) ) | ~spl2_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl2_10 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl2_10 | ~spl2_8 | ~spl2_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f78,f74,f69,f80])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl2_8 <=> ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl2_9 <=> ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) ) | (~spl2_8 | ~spl2_9)),
% 0.21/0.52    inference(subsumption_resolution,[],[f77,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ) | ~spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0) ) | ~spl2_9),
% 0.21/0.52    inference(resolution,[],[f75,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) | ~r1_tarski(X0,k1_relat_1(sK1))) ) | ~spl2_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl2_9 | ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f55,f29,f74])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    spl2_1 <=> v1_relat_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK1)) | r1_tarski(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0)))) ) | ~spl2_1),
% 0.21/0.52    inference(resolution,[],[f21,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    v1_relat_1(sK1) | ~spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f29])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl2_8 | ~spl2_1 | ~spl2_2 | ~spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f67,f39,f34,f29,f69])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    spl2_2 <=> v1_funct_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl2_3 <=> v2_funct_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f31])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_relat_1(sK1)) ) | (~spl2_2 | ~spl2_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f65,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    v1_funct_1(sK1) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f34])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) ) | ~spl2_3),
% 0.21/0.52    inference(resolution,[],[f22,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    v2_funct_1(sK1) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_funct_1(X1) | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ~spl2_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f20,f49])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK0 != k10_relat_1(sK1,k9_relat_1(sK1,sK0)) & v2_funct_1(sK1) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ? [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) != X0 & (v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1)))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f4])).
% 0.21/0.52  fof(f4,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f44])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f39])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    v2_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f34])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f16,f29])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (14064)------------------------------
% 0.21/0.52  % (14064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14064)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (14064)Memory used [KB]: 6140
% 0.21/0.52  % (14064)Time elapsed: 0.101 s
% 0.21/0.52  % (14064)------------------------------
% 0.21/0.52  % (14064)------------------------------
% 0.21/0.52  % (14061)Success in time 0.162 s
%------------------------------------------------------------------------------
