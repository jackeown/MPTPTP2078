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
% DateTime   : Thu Dec  3 12:46:51 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 296 expanded)
%              Number of leaves         :   16 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  181 ( 495 expanded)
%              Number of equality atoms :   22 ( 185 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f634,f646,f647])).

fof(f647,plain,
    ( spl2_2
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f640])).

fof(f640,plain,
    ( $false
    | spl2_2
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f22,f58,f131,f529,f498])).

fof(f498,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_relat_1(X4),k1_relat_1(X5))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f321,f49])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f321,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_relat_1(X1))
      | r1_tarski(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f145,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f145,plain,(
    ! [X12,X13,X11] :
      ( r1_tarski(X13,k1_relat_1(k3_tarski(k1_enumset1(X11,X11,X12))))
      | ~ r1_tarski(X13,k1_relat_1(X12))
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f25,f40,f40])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f529,plain,
    ( v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl2_14
  <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f131,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f58,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2) ),
    inference(superposition,[],[f44,f45])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f646,plain,
    ( spl2_1
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f639])).

fof(f639,plain,
    ( $false
    | spl2_1
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f24,f44,f127,f529,f498])).

fof(f127,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f634,plain,(
    spl2_14 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | spl2_14 ),
    inference(unit_resulting_resolution,[],[f22,f49,f530,f439])).

fof(f439,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_setfam_1(k1_enumset1(X1,X1,X0)))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X2) ) ),
    inference(superposition,[],[f418,f45])).

fof(f418,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,k1_setfam_1(k1_enumset1(X5,X5,X6)))
      | ~ v1_relat_1(X5)
      | v1_relat_1(X4) ) ),
    inference(resolution,[],[f348,f49])).

fof(f348,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_tarski(X5,k1_setfam_1(k1_enumset1(X3,X3,X6)))
      | ~ r1_tarski(X4,X5)
      | ~ v1_relat_1(X3)
      | v1_relat_1(X4) ) ),
    inference(resolution,[],[f346,f44])).

fof(f346,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X3)
      | v1_relat_1(X0) ) ),
    inference(condensation,[],[f340])).

fof(f340,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X3,X4)
      | v1_relat_1(X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f113,f97])).

fof(f97,plain,(
    ! [X8,X7,X9] :
      ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(X9,X9,X8)))
      | ~ r1_tarski(X7,X9)
      | v1_relat_1(X7)
      | ~ r1_tarski(X7,X8) ) ),
    inference(resolution,[],[f48,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f113,plain,(
    ! [X10,X8,X11,X9] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X8,X8,X9)))
      | ~ v1_relat_1(X10)
      | ~ r1_tarski(X11,X10)
      | ~ r1_tarski(X9,X11) ) ),
    inference(resolution,[],[f107,f81])).

fof(f81,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(k1_setfam_1(k1_enumset1(X5,X5,X6)),X7)
      | ~ r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f77,f58])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(X2,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f47,f67])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f70,f67])).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_relat_1(k3_tarski(k1_enumset1(X5,X5,X4)))
      | v1_relat_1(X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f47,f52])).

fof(f530,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f528])).

fof(f132,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f123,f129,f125])).

fof(f123,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK0)) ),
    inference(resolution,[],[f42,f48])).

fof(f42,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f23,f41,f41])).

fof(f23,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (26308)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (26324)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (26316)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (26307)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (26318)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (26324)Refutation not found, incomplete strategy% (26324)------------------------------
% 0.21/0.52  % (26324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26310)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (26303)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.53  % (26323)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.28/0.53  % (26319)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.28/0.53  % (26311)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.28/0.53  % (26302)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.53  % (26296)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.53  % (26315)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.28/0.53  % (26298)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.28/0.54  % (26300)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.54  % (26299)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.54  % (26325)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.28/0.54  % (26297)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.54  % (26325)Refutation not found, incomplete strategy% (26325)------------------------------
% 1.28/0.54  % (26325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (26325)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (26325)Memory used [KB]: 1663
% 1.28/0.54  % (26325)Time elapsed: 0.137 s
% 1.28/0.54  % (26325)------------------------------
% 1.28/0.54  % (26325)------------------------------
% 1.28/0.54  % (26306)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.28/0.54  % (26301)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.54  % (26306)Refutation not found, incomplete strategy% (26306)------------------------------
% 1.28/0.54  % (26306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (26306)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (26306)Memory used [KB]: 10746
% 1.28/0.54  % (26306)Time elapsed: 0.133 s
% 1.28/0.54  % (26306)------------------------------
% 1.28/0.54  % (26306)------------------------------
% 1.28/0.54  % (26324)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (26324)Memory used [KB]: 10618
% 1.28/0.54  % (26324)Time elapsed: 0.116 s
% 1.28/0.54  % (26324)------------------------------
% 1.28/0.54  % (26324)------------------------------
% 1.28/0.54  % (26321)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.28/0.54  % (26310)Refutation not found, incomplete strategy% (26310)------------------------------
% 1.28/0.54  % (26310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (26310)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (26310)Memory used [KB]: 1918
% 1.28/0.54  % (26310)Time elapsed: 0.085 s
% 1.28/0.54  % (26310)------------------------------
% 1.28/0.54  % (26310)------------------------------
% 1.49/0.55  % (26314)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.49/0.55  % (26313)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.55  % (26317)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.55  % (26322)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (26322)Refutation not found, incomplete strategy% (26322)------------------------------
% 1.49/0.55  % (26322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (26322)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.55  
% 1.49/0.55  % (26322)Memory used [KB]: 6268
% 1.49/0.55  % (26322)Time elapsed: 0.148 s
% 1.49/0.55  % (26322)------------------------------
% 1.49/0.55  % (26322)------------------------------
% 1.49/0.55  % (26305)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.49/0.56  % (26312)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.56  % (26312)Refutation not found, incomplete strategy% (26312)------------------------------
% 1.49/0.56  % (26312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (26312)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (26312)Memory used [KB]: 10618
% 1.49/0.56  % (26312)Time elapsed: 0.147 s
% 1.49/0.56  % (26312)------------------------------
% 1.49/0.56  % (26312)------------------------------
% 1.49/0.56  % (26309)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.49/0.56  % (26304)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.57  % (26297)Refutation not found, incomplete strategy% (26297)------------------------------
% 1.49/0.57  % (26297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (26297)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (26297)Memory used [KB]: 1791
% 1.49/0.57  % (26297)Time elapsed: 0.135 s
% 1.49/0.57  % (26297)------------------------------
% 1.49/0.57  % (26297)------------------------------
% 1.49/0.57  % (26320)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.49/0.57  % (26320)Refutation not found, incomplete strategy% (26320)------------------------------
% 1.49/0.57  % (26320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (26320)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (26320)Memory used [KB]: 10746
% 1.49/0.57  % (26320)Time elapsed: 0.170 s
% 1.49/0.57  % (26320)------------------------------
% 1.49/0.57  % (26320)------------------------------
% 1.49/0.62  % (26309)Refutation found. Thanks to Tanya!
% 1.49/0.62  % SZS status Theorem for theBenchmark
% 1.49/0.62  % SZS output start Proof for theBenchmark
% 1.49/0.62  fof(f648,plain,(
% 1.49/0.62    $false),
% 1.49/0.62    inference(avatar_sat_refutation,[],[f132,f634,f646,f647])).
% 1.49/0.62  fof(f647,plain,(
% 1.49/0.62    spl2_2 | ~spl2_14),
% 1.49/0.62    inference(avatar_contradiction_clause,[],[f640])).
% 1.49/0.62  fof(f640,plain,(
% 1.49/0.62    $false | (spl2_2 | ~spl2_14)),
% 1.49/0.62    inference(unit_resulting_resolution,[],[f22,f58,f131,f529,f498])).
% 1.49/0.62  fof(f498,plain,(
% 1.49/0.62    ( ! [X4,X5] : (r1_tarski(k1_relat_1(X4),k1_relat_1(X5)) | ~v1_relat_1(X4) | ~v1_relat_1(X5) | ~r1_tarski(X4,X5)) )),
% 1.49/0.62    inference(resolution,[],[f321,f49])).
% 1.49/0.62  fof(f49,plain,(
% 1.49/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.62    inference(equality_resolution,[],[f34])).
% 1.49/0.62  fof(f34,plain,(
% 1.49/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.49/0.62    inference(cnf_transformation,[],[f1])).
% 1.49/0.62  fof(f1,axiom,(
% 1.49/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.62  fof(f321,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_relat_1(X1)) | r1_tarski(X2,k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(X1,X0)) )),
% 1.49/0.62    inference(superposition,[],[f145,f67])).
% 1.49/0.62  fof(f67,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.62    inference(superposition,[],[f46,f45])).
% 1.49/0.62  fof(f45,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.49/0.62    inference(definition_unfolding,[],[f28,f31,f31])).
% 1.49/0.62  fof(f31,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f7])).
% 1.49/0.62  fof(f7,axiom,(
% 1.49/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.49/0.62  fof(f28,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f6])).
% 1.49/0.62  fof(f6,axiom,(
% 1.49/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.49/0.62  fof(f46,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.62    inference(definition_unfolding,[],[f32,f40])).
% 1.49/0.62  fof(f40,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.49/0.62    inference(definition_unfolding,[],[f29,f31])).
% 1.49/0.62  fof(f29,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f8])).
% 1.49/0.62  fof(f8,axiom,(
% 1.49/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.49/0.62  fof(f32,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.49/0.62    inference(cnf_transformation,[],[f18])).
% 1.49/0.62  fof(f18,plain,(
% 1.49/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.49/0.62    inference(ennf_transformation,[],[f3])).
% 1.49/0.62  fof(f3,axiom,(
% 1.49/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.49/0.62  fof(f145,plain,(
% 1.49/0.62    ( ! [X12,X13,X11] : (r1_tarski(X13,k1_relat_1(k3_tarski(k1_enumset1(X11,X11,X12)))) | ~r1_tarski(X13,k1_relat_1(X12)) | ~v1_relat_1(X12) | ~v1_relat_1(X11)) )),
% 1.49/0.62    inference(superposition,[],[f47,f43])).
% 1.49/0.62  fof(f43,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k1_relat_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.62    inference(definition_unfolding,[],[f25,f40,f40])).
% 1.49/0.62  fof(f25,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f16])).
% 1.49/0.62  fof(f16,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f12])).
% 1.49/0.62  fof(f12,axiom,(
% 1.49/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).
% 1.49/0.62  fof(f47,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.49/0.62    inference(definition_unfolding,[],[f38,f40])).
% 1.49/0.62  fof(f38,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f19])).
% 1.49/0.62  fof(f19,plain,(
% 1.49/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.49/0.62    inference(ennf_transformation,[],[f2])).
% 1.49/0.62  fof(f2,axiom,(
% 1.49/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.49/0.62  fof(f529,plain,(
% 1.49/0.62    v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | ~spl2_14),
% 1.49/0.62    inference(avatar_component_clause,[],[f528])).
% 1.49/0.62  fof(f528,plain,(
% 1.49/0.62    spl2_14 <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 1.49/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.49/0.62  fof(f131,plain,(
% 1.49/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK1)) | spl2_2),
% 1.49/0.62    inference(avatar_component_clause,[],[f129])).
% 1.49/0.62  fof(f129,plain,(
% 1.49/0.62    spl2_2 <=> r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK1))),
% 1.49/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.49/0.62  fof(f58,plain,(
% 1.49/0.62    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2)) )),
% 1.49/0.62    inference(superposition,[],[f44,f45])).
% 1.49/0.62  fof(f44,plain,(
% 1.49/0.62    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.49/0.62    inference(definition_unfolding,[],[f27,f41])).
% 1.49/0.62  fof(f41,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.49/0.62    inference(definition_unfolding,[],[f30,f31])).
% 1.49/0.62  fof(f30,plain,(
% 1.49/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f9])).
% 1.49/0.62  fof(f9,axiom,(
% 1.49/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.49/0.62  fof(f27,plain,(
% 1.49/0.62    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f4])).
% 1.49/0.62  fof(f4,axiom,(
% 1.49/0.62    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.49/0.62  fof(f22,plain,(
% 1.49/0.62    v1_relat_1(sK1)),
% 1.49/0.62    inference(cnf_transformation,[],[f15])).
% 1.49/0.62  fof(f15,plain,(
% 1.49/0.62    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f14])).
% 1.49/0.62  fof(f14,negated_conjecture,(
% 1.49/0.62    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.49/0.62    inference(negated_conjecture,[],[f13])).
% 1.49/0.62  fof(f13,conjecture,(
% 1.49/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 1.49/0.62  fof(f646,plain,(
% 1.49/0.62    spl2_1 | ~spl2_14),
% 1.49/0.62    inference(avatar_contradiction_clause,[],[f639])).
% 1.49/0.62  fof(f639,plain,(
% 1.49/0.62    $false | (spl2_1 | ~spl2_14)),
% 1.49/0.62    inference(unit_resulting_resolution,[],[f24,f44,f127,f529,f498])).
% 1.49/0.62  fof(f127,plain,(
% 1.49/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK0)) | spl2_1),
% 1.49/0.62    inference(avatar_component_clause,[],[f125])).
% 1.49/0.62  fof(f125,plain,(
% 1.49/0.62    spl2_1 <=> r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK0))),
% 1.49/0.62    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.49/0.62  fof(f24,plain,(
% 1.49/0.62    v1_relat_1(sK0)),
% 1.49/0.62    inference(cnf_transformation,[],[f15])).
% 1.49/0.62  fof(f634,plain,(
% 1.49/0.62    spl2_14),
% 1.49/0.62    inference(avatar_contradiction_clause,[],[f604])).
% 1.49/0.62  fof(f604,plain,(
% 1.49/0.62    $false | spl2_14),
% 1.49/0.62    inference(unit_resulting_resolution,[],[f22,f49,f530,f439])).
% 1.49/0.62  fof(f439,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_setfam_1(k1_enumset1(X1,X1,X0))) | ~v1_relat_1(X0) | v1_relat_1(X2)) )),
% 1.49/0.62    inference(superposition,[],[f418,f45])).
% 1.49/0.62  fof(f418,plain,(
% 1.49/0.62    ( ! [X6,X4,X5] : (~r1_tarski(X4,k1_setfam_1(k1_enumset1(X5,X5,X6))) | ~v1_relat_1(X5) | v1_relat_1(X4)) )),
% 1.49/0.62    inference(resolution,[],[f348,f49])).
% 1.49/0.62  fof(f348,plain,(
% 1.49/0.62    ( ! [X6,X4,X5,X3] : (~r1_tarski(X5,k1_setfam_1(k1_enumset1(X3,X3,X6))) | ~r1_tarski(X4,X5) | ~v1_relat_1(X3) | v1_relat_1(X4)) )),
% 1.49/0.62    inference(resolution,[],[f346,f44])).
% 1.49/0.62  fof(f346,plain,(
% 1.49/0.62    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1) | ~r1_tarski(X1,X3) | v1_relat_1(X0)) )),
% 1.49/0.62    inference(condensation,[],[f340])).
% 1.49/0.62  fof(f340,plain,(
% 1.49/0.62    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X0) | ~r1_tarski(X2,X1) | ~r1_tarski(X3,X4) | v1_relat_1(X3) | ~r1_tarski(X3,X2)) )),
% 1.49/0.62    inference(resolution,[],[f113,f97])).
% 1.49/0.62  fof(f97,plain,(
% 1.49/0.62    ( ! [X8,X7,X9] : (~v1_relat_1(k1_setfam_1(k1_enumset1(X9,X9,X8))) | ~r1_tarski(X7,X9) | v1_relat_1(X7) | ~r1_tarski(X7,X8)) )),
% 1.49/0.62    inference(resolution,[],[f48,f52])).
% 1.49/0.62  fof(f52,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.49/0.62    inference(resolution,[],[f26,f36])).
% 1.49/0.62  fof(f36,plain,(
% 1.49/0.62    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f10])).
% 1.49/0.62  fof(f10,axiom,(
% 1.49/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.62  fof(f26,plain,(
% 1.49/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.49/0.62    inference(cnf_transformation,[],[f17])).
% 1.49/0.62  fof(f17,plain,(
% 1.49/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.49/0.62    inference(ennf_transformation,[],[f11])).
% 1.49/0.62  fof(f11,axiom,(
% 1.49/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.49/0.62  fof(f48,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.49/0.62    inference(definition_unfolding,[],[f39,f41])).
% 1.49/0.62  fof(f39,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.49/0.62    inference(cnf_transformation,[],[f21])).
% 1.49/0.62  fof(f21,plain,(
% 1.49/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.49/0.62    inference(flattening,[],[f20])).
% 1.49/0.62  fof(f20,plain,(
% 1.49/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.49/0.62    inference(ennf_transformation,[],[f5])).
% 1.49/0.62  fof(f5,axiom,(
% 1.49/0.62    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.49/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.49/0.62  fof(f113,plain,(
% 1.49/0.62    ( ! [X10,X8,X11,X9] : (v1_relat_1(k1_setfam_1(k1_enumset1(X8,X8,X9))) | ~v1_relat_1(X10) | ~r1_tarski(X11,X10) | ~r1_tarski(X9,X11)) )),
% 1.49/0.62    inference(resolution,[],[f107,f81])).
% 1.49/0.62  fof(f81,plain,(
% 1.49/0.62    ( ! [X6,X7,X5] : (r1_tarski(k1_setfam_1(k1_enumset1(X5,X5,X6)),X7) | ~r1_tarski(X6,X7)) )),
% 1.49/0.62    inference(resolution,[],[f77,f58])).
% 1.49/0.62  fof(f77,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(X2,X0) | ~r1_tarski(X1,X0)) )),
% 1.49/0.62    inference(superposition,[],[f47,f67])).
% 1.49/0.62  fof(f107,plain,(
% 1.49/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | v1_relat_1(X2) | ~v1_relat_1(X0) | ~r1_tarski(X1,X0)) )),
% 1.49/0.62    inference(superposition,[],[f70,f67])).
% 1.49/0.62  fof(f70,plain,(
% 1.49/0.62    ( ! [X4,X5,X3] : (~v1_relat_1(k3_tarski(k1_enumset1(X5,X5,X4))) | v1_relat_1(X3) | ~r1_tarski(X3,X4)) )),
% 1.49/0.62    inference(resolution,[],[f47,f52])).
% 1.49/0.62  fof(f530,plain,(
% 1.49/0.62    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_14),
% 1.49/0.62    inference(avatar_component_clause,[],[f528])).
% 1.49/0.62  fof(f132,plain,(
% 1.49/0.62    ~spl2_1 | ~spl2_2),
% 1.49/0.62    inference(avatar_split_clause,[],[f123,f129,f125])).
% 1.49/0.62  fof(f123,plain,(
% 1.49/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_relat_1(sK0))),
% 1.49/0.62    inference(resolution,[],[f42,f48])).
% 1.49/0.62  fof(f42,plain,(
% 1.49/0.62    ~r1_tarski(k1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 1.49/0.62    inference(definition_unfolding,[],[f23,f41,f41])).
% 1.49/0.62  fof(f23,plain,(
% 1.49/0.62    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 1.49/0.62    inference(cnf_transformation,[],[f15])).
% 1.49/0.62  % SZS output end Proof for theBenchmark
% 1.49/0.62  % (26309)------------------------------
% 1.49/0.62  % (26309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.62  % (26309)Termination reason: Refutation
% 1.49/0.62  
% 1.49/0.62  % (26309)Memory used [KB]: 6652
% 1.49/0.62  % (26309)Time elapsed: 0.199 s
% 1.49/0.62  % (26309)------------------------------
% 1.49/0.62  % (26309)------------------------------
% 1.49/0.62  % (26295)Success in time 0.252 s
%------------------------------------------------------------------------------
