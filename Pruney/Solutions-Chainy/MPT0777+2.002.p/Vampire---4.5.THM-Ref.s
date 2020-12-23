%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 141 expanded)
%              Number of leaves         :   19 (  61 expanded)
%              Depth                    :    7
%              Number of atoms          :  144 ( 259 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f40,f44,f50,f54,f60,f64,f68,f76,f85,f106])).

fof(f106,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f39,f103])).

fof(f103,plain,
    ( ! [X4,X3] : k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X3,X3,X4))) = k2_wellord1(k2_wellord1(sK2,X3),X4)
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f98,f59])).

fof(f59,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f98,plain,
    ( ! [X4,X3] : k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X3,X3,X4))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X3),k2_wellord1(sK2,X3),k2_zfmisc_1(X4,X4)))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f84,f49])).

fof(f49,plain,
    ( ! [X0] : k2_wellord1(sK2,X0) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(X0,X0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_5
  <=> ! [X0] : k2_wellord1(sK2,X0) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(X0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f84,plain,
    ( ! [X2,X0,X1] : k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2))) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X2)))))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] : k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2))) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f39,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_3
  <=> k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( spl3_11
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f80,f74,f66,f83])).

fof(f66,plain,
    ( spl3_9
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f74,plain,
    ( spl3_10
  <=> ! [X1,X0] : k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0),X1)))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f80,plain,
    ( ! [X2,X0,X1] : k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2))) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X2)))))
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(superposition,[],[f75,f67])).

fof(f67,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( ! [X0,X1] : k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0),X1)))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f76,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f69,f62,f48,f74])).

fof(f62,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] : k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( ! [X0,X1] : k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0),X1)))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),X1))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(superposition,[],[f63,f49])).

fof(f63,plain,
    ( ! [X2,X0,X1] : k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f68,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f21,f22,f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f64,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f62])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) ),
    inference(definition_unfolding,[],[f20,f22,f22,f22,f22])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f60,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f55,f52,f28,f58])).

fof(f28,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X1,X3,X2] :
        ( k2_wellord1(k2_wellord1(X1,X2),X3) = k1_setfam_1(k1_enumset1(k2_wellord1(X1,X2),k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f53,f30])).

fof(f30,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f53,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X1)
        | k2_wellord1(k2_wellord1(X1,X2),X3) = k1_setfam_1(k1_enumset1(k2_wellord1(X1,X2),k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3))) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f54,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f46,f42,f33,f52])).

fof(f33,plain,
    ( spl3_2
  <=> ! [X1,X0] :
        ( v1_relat_1(k2_wellord1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( k2_wellord1(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f46,plain,
    ( ! [X2,X3,X1] :
        ( k2_wellord1(k2_wellord1(X1,X2),X3) = k1_setfam_1(k1_enumset1(k2_wellord1(X1,X2),k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3)))
        | ~ v1_relat_1(X1) )
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f43,f34])).

fof(f34,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k2_wellord1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k2_wellord1(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1))) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f50,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f45,f42,f28,f48])).

fof(f45,plain,
    ( ! [X0] : k2_wellord1(sK2,X0) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(X0,X0)))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(resolution,[],[f43,f30])).

fof(f44,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(f40,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f23,f37])).

fof(f23,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f22])).

fof(f15,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1))
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f33])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (8186)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (8194)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (8187)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (8182)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (8190)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (8195)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (8189)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (8185)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (8196)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (8190)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f31,f35,f40,f44,f50,f54,f60,f64,f68,f76,f85,f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_11),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f104])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    $false | (spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f39,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X4,X3] : (k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X3,X3,X4))) = k2_wellord1(k2_wellord1(sK2,X3),X4)) ) | (~spl3_5 | ~spl3_7 | ~spl3_11)),
% 0.20/0.48    inference(forward_demodulation,[],[f98,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)))) ) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl3_7 <=> ! [X1,X0] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X4,X3] : (k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X3,X3,X4))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X3),k2_wellord1(sK2,X3),k2_zfmisc_1(X4,X4)))) ) | (~spl3_5 | ~spl3_11)),
% 0.20/0.48    inference(superposition,[],[f84,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0] : (k2_wellord1(sK2,X0) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(X0,X0)))) ) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl3_5 <=> ! [X0] : k2_wellord1(sK2,X0) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(X0,X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2))) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X2)))))) ) | ~spl3_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl3_11 <=> ! [X1,X0,X2] : k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2))) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X2)))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl3_3 <=> k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl3_11 | ~spl3_9 | ~spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f80,f74,f66,f83])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl3_9 <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl3_10 <=> ! [X1,X0] : k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0),X1)))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X2))) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X2)))))) ) | (~spl3_9 | ~spl3_10)),
% 0.20/0.48    inference(superposition,[],[f75,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) ) | ~spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f66])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0),X1)))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),X1))) ) | ~spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f74])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_10 | ~spl3_5 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f69,f62,f48,f74])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl3_8 <=> ! [X1,X0,X2] : k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X0),k2_zfmisc_1(X0,X0),X1)))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),X1))) ) | (~spl3_5 | ~spl3_8)),
% 0.20/0.49    inference(superposition,[],[f63,f49])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2))))) ) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f62])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f66])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f21,f22,f22,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f17,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f62])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2))))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f20,f22,f22,f22,f22])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    spl3_7 | ~spl3_1 | ~spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f55,f52,f28,f58])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_6 <=> ! [X1,X3,X2] : (k2_wellord1(k2_wellord1(X1,X2),X3) = k1_setfam_1(k1_enumset1(k2_wellord1(X1,X2),k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3))) | ~v1_relat_1(X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0),k2_wellord1(sK2,X0),k2_zfmisc_1(X1,X1)))) ) | (~spl3_1 | ~spl3_6)),
% 0.20/0.49    inference(resolution,[],[f53,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f28])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k2_wellord1(k2_wellord1(X1,X2),X3) = k1_setfam_1(k1_enumset1(k2_wellord1(X1,X2),k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3)))) ) | ~spl3_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f52])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl3_6 | ~spl3_2 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f42,f33,f52])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl3_2 <=> ! [X1,X0] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    spl3_4 <=> ! [X1,X0] : (k2_wellord1(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1))) | ~v1_relat_1(X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X3,X1] : (k2_wellord1(k2_wellord1(X1,X2),X3) = k1_setfam_1(k1_enumset1(k2_wellord1(X1,X2),k2_wellord1(X1,X2),k2_zfmisc_1(X3,X3))) | ~v1_relat_1(X1)) ) | (~spl3_2 | ~spl3_4)),
% 0.20/0.49    inference(resolution,[],[f43,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f33])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1)))) ) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f42])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl3_5 | ~spl3_1 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f42,f28,f48])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0] : (k2_wellord1(sK2,X0) = k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(X0,X0)))) ) | (~spl3_1 | ~spl3_4)),
% 0.20/0.49    inference(resolution,[],[f43,f30])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f24,f42])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1))) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f16,f22])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f37])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.49    inference(definition_unfolding,[],[f15,f22])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1)) & v1_relat_1(X2)) => (k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) != k2_wellord1(X2,k3_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f19,f33])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f14,f28])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    v1_relat_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (8190)------------------------------
% 0.20/0.49  % (8190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (8190)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (8190)Memory used [KB]: 6268
% 0.20/0.49  % (8190)Time elapsed: 0.014 s
% 0.20/0.49  % (8190)------------------------------
% 0.20/0.49  % (8190)------------------------------
% 0.20/0.49  % (8191)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (8181)Success in time 0.133 s
%------------------------------------------------------------------------------
