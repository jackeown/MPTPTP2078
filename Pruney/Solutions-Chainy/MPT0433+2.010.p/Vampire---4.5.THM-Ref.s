%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 284 expanded)
%              Number of leaves         :   19 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 421 expanded)
%              Number of equality atoms :   24 ( 192 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f247,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f181,f191,f215,f217,f246])).

fof(f246,plain,
    ( spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl2_2
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f23,f175,f74,f128,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f153,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f153,plain,(
    ! [X6,X5] :
      ( r1_tarski(k1_relat_1(X5),k1_relat_1(k3_tarski(k2_enumset1(X5,X5,X5,X6))))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f60,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f26,f44,f44])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(resolution,[],[f50,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f128,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl2_2
  <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f74,plain,(
    ! [X6,X5] : r1_tarski(k1_setfam_1(k2_enumset1(X6,X6,X6,X5)),X5) ),
    inference(superposition,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f29,f43,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f175,plain,
    ( v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl2_4
  <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f217,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f25,f180])).

fof(f180,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl2_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f25,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f215,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f23,f74,f176,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f176,plain,
    ( ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f174])).

fof(f191,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f47,f52,f172,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f50,f49])).

fof(f172,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl2_3
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f181,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f164,f122,f178,f174,f170])).

fof(f122,plain,
    ( spl2_1
  <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f164,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl2_1 ),
    inference(resolution,[],[f162,f124])).

fof(f124,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f129,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f120,f126,f122])).

fof(f120,plain,
    ( ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) ),
    inference(resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f45,plain,(
    ~ r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f24,f43,f43])).

fof(f24,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:39:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (4827)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.48  % (4827)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (4835)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f129,f181,f191,f215,f217,f246])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    spl2_2 | ~spl2_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f244])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    $false | (spl2_2 | ~spl2_4)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f23,f175,f74,f128,f162])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(superposition,[],[f153,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f33,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f30,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f32,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ( ! [X6,X5] : (r1_tarski(k1_relat_1(X5),k1_relat_1(k3_tarski(k2_enumset1(X5,X5,X5,X6)))) | ~v1_relat_1(X6) | ~v1_relat_1(X5)) )),
% 0.20/0.50    inference(superposition,[],[f60,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(k3_tarski(k2_enumset1(X0,X0,X0,X1))) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f26,f44,f44])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.20/0.50    inference(resolution,[],[f50,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f40,f44])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) | spl2_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl2_2 <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X6,X5] : (r1_tarski(k1_setfam_1(k2_enumset1(X6,X6,X6,X5)),X5)) )),
% 0.20/0.50    inference(superposition,[],[f47,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f29,f43,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f31,f42])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f28,f43])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | ~spl2_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f174])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    spl2_4 <=> v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    v1_relat_1(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    spl2_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    $false | spl2_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f25,f180])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ~v1_relat_1(sK0) | spl2_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f178])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    spl2_5 <=> v1_relat_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    v1_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    spl2_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f201])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    $false | spl2_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f23,f74,f176,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f27,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl2_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f174])).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    spl2_3),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.50  fof(f185,plain,(
% 0.20/0.50    $false | spl2_3),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f47,f52,f172,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(superposition,[],[f50,f49])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl2_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f170])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    spl2_3 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f164,f122,f178,f174,f170])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    spl2_1 <=> r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl2_1),
% 0.20/0.50    inference(resolution,[],[f162,f124])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0)) | spl2_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f122])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    ~spl2_1 | ~spl2_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f120,f126,f122])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK1)) | ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_relat_1(sK0))),
% 0.20/0.50    inference(resolution,[],[f45,f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f41,f43])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))),k1_setfam_1(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK1))))),
% 0.20/0.50    inference(definition_unfolding,[],[f24,f43,f43])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ~r1_tarski(k1_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (4827)------------------------------
% 0.20/0.50  % (4827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4827)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (4827)Memory used [KB]: 6396
% 0.20/0.50  % (4827)Time elapsed: 0.084 s
% 0.20/0.50  % (4827)------------------------------
% 0.20/0.50  % (4827)------------------------------
% 0.20/0.50  % (4813)Success in time 0.148 s
%------------------------------------------------------------------------------
