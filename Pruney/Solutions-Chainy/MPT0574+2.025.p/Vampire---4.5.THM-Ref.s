%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  102 ( 154 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f94,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f68,f93])).

fof(f93,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f90,f25])).

fof(f25,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f90,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1))
    | ~ spl3_1
    | spl3_3
    | ~ spl3_6 ),
    inference(superposition,[],[f80,f67])).

fof(f67,plain,
    ( sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_6
  <=> sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f80,plain,
    ( ! [X0] : ~ r1_tarski(k10_relat_1(sK2,k2_xboole_0(sK0,X0)),k10_relat_1(sK2,sK1))
    | ~ spl3_1
    | spl3_3 ),
    inference(superposition,[],[f42,f61])).

fof(f61,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f30,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f30,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f42,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f40,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f40,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f48,f33,f65])).

fof(f33,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f35,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f35,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f41,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21891)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.47  % (21901)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.48  % (21886)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.48  % (21909)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.48  % (21892)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.48  % (21887)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.48  % (21909)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (21904)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.49  % (21900)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f31,f36,f41,f68,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ~spl3_1 | spl3_3 | ~spl3_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    $false | (~spl3_1 | spl3_3 | ~spl3_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f90,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ~r1_tarski(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK1)) | (~spl3_1 | spl3_3 | ~spl3_6)),
% 0.20/0.49    inference(superposition,[],[f80,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl3_6 <=> sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k10_relat_1(sK2,k2_xboole_0(sK0,X0)),k10_relat_1(sK2,sK1))) ) | (~spl3_1 | spl3_3)),
% 0.20/0.49    inference(superposition,[],[f42,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_1),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f30,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k2_xboole_0(k10_relat_1(sK2,sK0),X0),k10_relat_1(sK2,sK1))) ) | spl3_3),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    spl3_3 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_6 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f48,f33,f65])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl3_2),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f35,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f33])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f18,f38])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f5])).
% 0.20/0.49  fof(f5,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f33])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f16,f28])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (21909)------------------------------
% 0.20/0.49  % (21909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21909)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (21909)Memory used [KB]: 10618
% 0.20/0.49  % (21909)Time elapsed: 0.082 s
% 0.20/0.49  % (21909)------------------------------
% 0.20/0.49  % (21909)------------------------------
% 0.20/0.49  % (21898)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (21902)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.49  % (21896)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (21885)Success in time 0.132 s
%------------------------------------------------------------------------------
