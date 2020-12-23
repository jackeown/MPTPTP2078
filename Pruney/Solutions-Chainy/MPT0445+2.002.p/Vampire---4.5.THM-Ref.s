%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  91 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  120 ( 214 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f77,f95,f101,f103])).

fof(f103,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f100,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).

fof(f100,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f101,plain,
    ( ~ spl2_4
    | ~ spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f96,f65,f57,f98])).

fof(f57,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f65,plain,
    ( spl2_3
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f96,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl2_3 ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    ! [X10,X11] :
      ( r1_tarski(k2_relat_1(X10),k2_relat_1(k2_xboole_0(X10,X11)))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X10) ) ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f67,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f95,plain,
    ( ~ spl2_2
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f94,f65,f57,f61])).

fof(f61,plain,
    ( spl2_2
  <=> v1_relat_1(k6_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f94,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f93,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f93,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f92,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f92,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1))))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f81,f26])).

fof(f81,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(k6_subset_1(sK0,sK1),sK1)))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f44,f45])).

fof(f45,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(k2_relat_1(X3),k2_relat_1(X2)) = k2_relat_1(k2_xboole_0(X2,X3))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f21,f26])).

fof(f44,plain,(
    ~ r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1)))) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f77,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f76])).

fof(f76,plain,
    ( $false
    | spl2_2 ),
    inference(resolution,[],[f71,f18])).

fof(f71,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_2 ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f63,plain,
    ( ~ v1_relat_1(k6_subset_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f70,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f59,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 09:40:56 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.44  % (15336)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.45  % (15345)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (15341)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (15340)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (15342)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (15340)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f70,f77,f95,f101,f103])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f102])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    $false | spl2_4),
% 0.20/0.46    inference(resolution,[],[f100,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    v1_relat_1(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f16,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    ~v1_relat_1(sK0) | spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    spl2_4 <=> v1_relat_1(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    ~spl2_4 | ~spl2_1 | spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f96,f65,f57,f98])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    spl2_1 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl2_3 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl2_3),
% 0.20/0.46    inference(resolution,[],[f67,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X10,X11] : (r1_tarski(k2_relat_1(X10),k2_relat_1(k2_xboole_0(X10,X11))) | ~v1_relat_1(X11) | ~v1_relat_1(X10)) )),
% 0.20/0.46    inference(superposition,[],[f23,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) | spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f65])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    ~spl2_2 | ~spl2_1 | ~spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f94,f65,f57,f61])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl2_2 <=> v1_relat_1(k6_subset_1(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK0,sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_subset_1(sK0,sK1))),
% 0.20/0.46    inference(forward_demodulation,[],[f93,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,sK0))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_subset_1(sK0,sK1))),
% 0.20/0.46    inference(forward_demodulation,[],[f92,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f27,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_subset_1(sK0,sK1))),
% 0.20/0.46    inference(forward_demodulation,[],[f81,f26])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(k2_xboole_0(k6_subset_1(sK0,sK1),sK1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_subset_1(sK0,sK1))),
% 0.20/0.46    inference(superposition,[],[f44,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X2,X3] : (k2_xboole_0(k2_relat_1(X3),k2_relat_1(X2)) = k2_relat_1(k2_xboole_0(X2,X3)) | ~v1_relat_1(X3) | ~v1_relat_1(X2)) )),
% 0.20/0.46    inference(superposition,[],[f21,f26])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(sK0),k2_xboole_0(k2_relat_1(sK1),k2_relat_1(k6_subset_1(sK0,sK1))))),
% 0.20/0.46    inference(resolution,[],[f30,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ~r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f28,f25])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    $false | spl2_2),
% 0.20/0.46    inference(resolution,[],[f71,f18])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ~v1_relat_1(sK0) | spl2_2),
% 0.20/0.46    inference(resolution,[],[f63,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(resolution,[],[f22,f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ~v1_relat_1(k6_subset_1(sK0,sK1)) | spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f61])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    spl2_1),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f69])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    $false | spl2_1),
% 0.20/0.46    inference(resolution,[],[f59,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f57])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (15340)------------------------------
% 0.20/0.46  % (15340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15340)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (15340)Memory used [KB]: 6140
% 0.20/0.46  % (15340)Time elapsed: 0.064 s
% 0.20/0.46  % (15340)------------------------------
% 0.20/0.46  % (15340)------------------------------
% 0.20/0.46  % (15351)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (15334)Success in time 0.115 s
%------------------------------------------------------------------------------
