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
% DateTime   : Thu Dec  3 12:47:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 112 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  148 ( 251 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f729,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f99,f103,f530,f543,f545,f548,f555,f725])).

fof(f725,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f724])).

fof(f724,plain,
    ( $false
    | spl5_9 ),
    inference(subsumption_resolution,[],[f554,f723])).

fof(f723,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(forward_demodulation,[],[f722,f59])).

% (27451)Refutation not found, incomplete strategy% (27451)------------------------------
% (27451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27451)Termination reason: Refutation not found, incomplete strategy

% (27451)Memory used [KB]: 10746
% (27451)Time elapsed: 0.169 s
% (27451)------------------------------
% (27451)------------------------------
fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f722,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,k1_xboole_0))),X0) ),
    inference(forward_demodulation,[],[f721,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f721,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0)),X0) ),
    inference(forward_demodulation,[],[f697,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f79,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f697,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))),X0) ),
    inference(superposition,[],[f88,f59])).

fof(f88,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f78,f67,f67])).

fof(f78,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f554,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f553])).

fof(f553,plain,
    ( spl5_9
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f555,plain,
    ( ~ spl5_7
    | ~ spl5_2
    | ~ spl5_9
    | spl5_6 ),
    inference(avatar_split_clause,[],[f549,f528,f553,f97,f537])).

fof(f537,plain,
    ( spl5_7
  <=> v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f97,plain,
    ( spl5_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f528,plain,
    ( spl5_6
  <=> r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f549,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl5_6 ),
    inference(resolution,[],[f529,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

% (27444)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f529,plain,
    ( ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f528])).

fof(f548,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f546])).

fof(f546,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f542,f65])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f542,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl5_8
  <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f545,plain,
    ( ~ spl5_3
    | spl5_7 ),
    inference(avatar_split_clause,[],[f544,f537,f101])).

fof(f101,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f544,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_7 ),
    inference(resolution,[],[f538,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f538,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f537])).

fof(f543,plain,
    ( ~ spl5_7
    | ~ spl5_3
    | ~ spl5_8
    | spl5_5 ),
    inference(avatar_split_clause,[],[f534,f525,f541,f101,f537])).

fof(f525,plain,
    ( spl5_5
  <=> r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f534,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl5_5 ),
    inference(resolution,[],[f526,f63])).

fof(f526,plain,
    ( ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f525])).

fof(f530,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f518,f93,f528,f525])).

fof(f93,plain,
    ( spl5_1
  <=> r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f518,plain,
    ( ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0))
    | spl5_1 ),
    inference(resolution,[],[f90,f94])).

fof(f94,plain,
    ( ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f81,f67])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f103,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f53,f101])).

fof(f53,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f99,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f54,f97])).

fof(f54,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f95,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f85,f93])).

fof(f85,plain,(
    ~ r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f55,f67,f67])).

fof(f55,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (27454)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (27469)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (27462)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (27446)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (27443)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (27443)Refutation not found, incomplete strategy% (27443)------------------------------
% 0.21/0.56  % (27443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (27443)Memory used [KB]: 1663
% 0.21/0.56  % (27443)Time elapsed: 0.155 s
% 0.21/0.56  % (27443)------------------------------
% 0.21/0.56  % (27443)------------------------------
% 0.21/0.56  % (27471)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (27464)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (27465)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (27457)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (27452)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (27456)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (27465)Refutation not found, incomplete strategy% (27465)------------------------------
% 0.21/0.58  % (27465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (27449)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (27465)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (27465)Memory used [KB]: 10746
% 0.21/0.58  % (27465)Time elapsed: 0.081 s
% 0.21/0.58  % (27465)------------------------------
% 0.21/0.58  % (27465)------------------------------
% 0.21/0.58  % (27468)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.58  % (27462)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.59  % (27461)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.59  % (27451)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.59  % (27453)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.59  % (27452)Refutation not found, incomplete strategy% (27452)------------------------------
% 0.21/0.59  % (27452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (27452)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (27452)Memory used [KB]: 10618
% 0.21/0.59  % (27452)Time elapsed: 0.169 s
% 0.21/0.59  % (27452)------------------------------
% 0.21/0.59  % (27452)------------------------------
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f729,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f95,f99,f103,f530,f543,f545,f548,f555,f725])).
% 0.21/0.59  fof(f725,plain,(
% 0.21/0.59    spl5_9),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f724])).
% 0.21/0.59  fof(f724,plain,(
% 0.21/0.59    $false | spl5_9),
% 0.21/0.59    inference(subsumption_resolution,[],[f554,f723])).
% 0.21/0.59  fof(f723,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f722,f59])).
% 0.21/0.59  % (27451)Refutation not found, incomplete strategy% (27451)------------------------------
% 0.21/0.59  % (27451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (27451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (27451)Memory used [KB]: 10746
% 0.21/0.59  % (27451)Time elapsed: 0.169 s
% 0.21/0.59  % (27451)------------------------------
% 0.21/0.59  % (27451)------------------------------
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.59    inference(cnf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,axiom,(
% 0.21/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.59  fof(f722,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,k1_xboole_0))),X0)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f721,f77])).
% 0.21/0.59  fof(f77,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.59  fof(f721,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0)),X0)) )),
% 0.21/0.59    inference(forward_demodulation,[],[f697,f89])).
% 0.21/0.59  fof(f89,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.59    inference(definition_unfolding,[],[f79,f67])).
% 0.21/0.59  fof(f67,plain,(
% 0.21/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f10])).
% 0.21/0.59  fof(f10,axiom,(
% 0.21/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.59  fof(f79,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.59  fof(f697,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))),X0)) )),
% 0.21/0.59    inference(superposition,[],[f88,f59])).
% 0.21/0.59  fof(f88,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2))) )),
% 0.21/0.59    inference(definition_unfolding,[],[f78,f67,f67])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.59  fof(f554,plain,(
% 0.21/0.59    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | spl5_9),
% 0.21/0.59    inference(avatar_component_clause,[],[f553])).
% 0.21/0.59  fof(f553,plain,(
% 0.21/0.59    spl5_9 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.59  fof(f555,plain,(
% 0.21/0.59    ~spl5_7 | ~spl5_2 | ~spl5_9 | spl5_6),
% 0.21/0.59    inference(avatar_split_clause,[],[f549,f528,f553,f97,f537])).
% 0.21/0.59  fof(f537,plain,(
% 0.21/0.59    spl5_7 <=> v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.59  fof(f97,plain,(
% 0.21/0.59    spl5_2 <=> v1_relat_1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.59  fof(f528,plain,(
% 0.21/0.59    spl5_6 <=> r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.59  fof(f549,plain,(
% 0.21/0.59    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl5_6),
% 0.21/0.59    inference(resolution,[],[f529,f63])).
% 0.21/0.59  fof(f63,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f30])).
% 0.21/0.60  % (27444)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(flattening,[],[f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,axiom,(
% 0.21/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.60  fof(f529,plain,(
% 0.21/0.60    ~r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1)) | spl5_6),
% 0.21/0.60    inference(avatar_component_clause,[],[f528])).
% 0.21/0.60  fof(f548,plain,(
% 0.21/0.60    spl5_8),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f546])).
% 0.21/0.60  fof(f546,plain,(
% 0.21/0.60    $false | spl5_8),
% 0.21/0.60    inference(resolution,[],[f542,f65])).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.60  fof(f542,plain,(
% 0.21/0.60    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | spl5_8),
% 0.21/0.60    inference(avatar_component_clause,[],[f541])).
% 0.21/0.60  fof(f541,plain,(
% 0.21/0.60    spl5_8 <=> r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.60  fof(f545,plain,(
% 0.21/0.60    ~spl5_3 | spl5_7),
% 0.21/0.60    inference(avatar_split_clause,[],[f544,f537,f101])).
% 0.21/0.60  fof(f101,plain,(
% 0.21/0.60    spl5_3 <=> v1_relat_1(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.60  fof(f544,plain,(
% 0.21/0.60    ~v1_relat_1(sK0) | spl5_7),
% 0.21/0.60    inference(resolution,[],[f538,f73])).
% 0.21/0.60  fof(f73,plain,(
% 0.21/0.60    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,axiom,(
% 0.21/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.60  fof(f538,plain,(
% 0.21/0.60    ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl5_7),
% 0.21/0.60    inference(avatar_component_clause,[],[f537])).
% 0.21/0.60  fof(f543,plain,(
% 0.21/0.60    ~spl5_7 | ~spl5_3 | ~spl5_8 | spl5_5),
% 0.21/0.60    inference(avatar_split_clause,[],[f534,f525,f541,f101,f537])).
% 0.21/0.60  fof(f525,plain,(
% 0.21/0.60    spl5_5 <=> r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.60  fof(f534,plain,(
% 0.21/0.60    ~r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl5_5),
% 0.21/0.60    inference(resolution,[],[f526,f63])).
% 0.21/0.60  fof(f526,plain,(
% 0.21/0.60    ~r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) | spl5_5),
% 0.21/0.60    inference(avatar_component_clause,[],[f525])).
% 0.21/0.60  fof(f530,plain,(
% 0.21/0.60    ~spl5_5 | ~spl5_6 | spl5_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f518,f93,f528,f525])).
% 0.21/0.60  fof(f93,plain,(
% 0.21/0.60    spl5_1 <=> r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.60  fof(f518,plain,(
% 0.21/0.60    ~r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_relat_1(sK0)) | spl5_1),
% 0.21/0.60    inference(resolution,[],[f90,f94])).
% 0.21/0.60  fof(f94,plain,(
% 0.21/0.60    ~r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))) | spl5_1),
% 0.21/0.60    inference(avatar_component_clause,[],[f93])).
% 0.21/0.60  fof(f90,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f81,f67])).
% 0.21/0.60  fof(f81,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(flattening,[],[f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.60  fof(f103,plain,(
% 0.21/0.60    spl5_3),
% 0.21/0.60    inference(avatar_split_clause,[],[f53,f101])).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    v1_relat_1(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f44])).
% 0.21/0.60  fof(f44,plain,(
% 0.21/0.60    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f43,f42])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f24])).
% 0.21/0.60  fof(f24,negated_conjecture,(
% 0.21/0.60    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.60    inference(negated_conjecture,[],[f23])).
% 0.21/0.60  fof(f23,conjecture,(
% 0.21/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 0.21/0.60  fof(f99,plain,(
% 0.21/0.60    spl5_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f54,f97])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    v1_relat_1(sK1)),
% 0.21/0.60    inference(cnf_transformation,[],[f44])).
% 0.21/0.60  fof(f95,plain,(
% 0.21/0.60    ~spl5_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f85,f93])).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    ~r1_tarski(k2_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k2_relat_1(sK0),k4_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))))),
% 0.21/0.60    inference(definition_unfolding,[],[f55,f67,f67])).
% 0.21/0.60  fof(f55,plain,(
% 0.21/0.60    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.60    inference(cnf_transformation,[],[f44])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (27462)------------------------------
% 0.21/0.60  % (27462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (27462)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (27462)Memory used [KB]: 11129
% 0.21/0.60  % (27462)Time elapsed: 0.157 s
% 0.21/0.60  % (27462)------------------------------
% 0.21/0.60  % (27462)------------------------------
% 1.92/0.60  % (27442)Success in time 0.243 s
%------------------------------------------------------------------------------
