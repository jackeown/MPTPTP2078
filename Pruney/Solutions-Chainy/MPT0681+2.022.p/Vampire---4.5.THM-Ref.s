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
% DateTime   : Thu Dec  3 12:53:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 385 expanded)
%              Number of leaves         :   23 ( 128 expanded)
%              Depth                    :   18
%              Number of atoms          :  227 ( 655 expanded)
%              Number of equality atoms :   50 ( 300 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f127,f140])).

fof(f140,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f138,f131])).

fof(f131,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f117,f130])).

fof(f130,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f128,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f128,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f65,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

% (26160)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f117,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f113,f40])).

fof(f113,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f105,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f66,f65])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f105,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f138,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f137,f126])).

fof(f126,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_6
  <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f137,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_xboole_0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(forward_demodulation,[],[f136,f130])).

fof(f136,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(forward_demodulation,[],[f135,f102])).

fof(f102,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_4
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f135,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(backward_demodulation,[],[f119,f133])).

fof(f133,plain,
    ( ! [X0,X1] : k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f76,f81,f86,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f71,f65])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f68,f65])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_setfam_1(k6_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f53,f63,f63])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

fof(f86,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f81,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f76,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f119,plain,
    ( r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))))
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f96,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f67,f65])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f96,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_5
  <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f127,plain,
    ( spl5_6
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f98,f74,f124])).

fof(f98,plain,
    ( k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f76,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f97,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f38,f94])).

fof(f38,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

fof(f92,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f36,f89])).

fof(f36,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f37,f84])).

fof(f37,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f35,f79])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f34,f74])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:24:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (26163)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (26165)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (26168)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (26164)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (26175)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (26175)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f127,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f117,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f128,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f65,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f39,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f42,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f43,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f52,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f54,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f55,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f56,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  % (26160)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f44,f63])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f113,f40])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f105,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f66,f65])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f46,f63])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f40,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k1_xboole_0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6)),
% 0.21/0.48    inference(forward_demodulation,[],[f137,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    spl5_6 <=> k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k1_xboole_0)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f136,f130])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK0))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f135,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f91,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK1) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl5_4 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_5)),
% 0.21/0.48    inference(backward_demodulation,[],[f119,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(k9_relat_1(sK2,X0),k4_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) = k9_relat_1(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f76,f81,f86,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) = k9_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f71,f65])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k4_xboole_0(k9_relat_1(X2,X0),k4_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f68,f65])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(X2,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_setfam_1(k6_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f53,f63,f63])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl5_3 <=> v2_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl5_2 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    v1_relat_1(sK2) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl5_1 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    r2_hidden(sK3(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k4_xboole_0(k9_relat_1(sK2,sK0),k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))) | spl5_5),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f96,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f67,f65])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f45,f63])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl5_5 <=> r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    spl5_6 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f74,f124])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK2,k1_xboole_0) | ~spl5_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f76,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f94])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v2_funct_1(sK2) & r1_xboole_0(sK0,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f16])).
% 0.21/0.49  fof(f16,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f36,f89])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f37,f84])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v2_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f79])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f74])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (26175)------------------------------
% 0.21/0.49  % (26175)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26175)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (26175)Memory used [KB]: 10618
% 0.21/0.49  % (26175)Time elapsed: 0.012 s
% 0.21/0.49  % (26175)------------------------------
% 0.21/0.49  % (26175)------------------------------
% 0.21/0.49  % (26172)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (26166)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (26159)Success in time 0.126 s
%------------------------------------------------------------------------------
