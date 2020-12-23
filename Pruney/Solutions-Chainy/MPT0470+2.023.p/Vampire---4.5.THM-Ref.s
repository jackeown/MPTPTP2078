%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 311 expanded)
%              Number of leaves         :   23 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  290 ( 664 expanded)
%              Number of equality atoms :   52 ( 152 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f810,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f76,f81,f126,f217,f222,f242,f281,f286,f801])).

fof(f801,plain,
    ( spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f799,f56])).

fof(f56,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_2
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f799,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f798,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | ~ spl2_3 ),
    inference(resolution,[],[f94,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f94,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f93,f70])).

fof(f70,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_3
  <=> v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f93,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f92,f59])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f46,f58])).

fof(f58,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f34,f46])).

% (3342)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f46,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f92,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ spl2_3 ),
    inference(superposition,[],[f41,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f90,f30])).

fof(f30,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f90,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f87,f66])).

fof(f66,plain,(
    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f62,f59])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(resolution,[],[f36,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f87,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))
    | ~ spl2_3 ),
    inference(resolution,[],[f37,f70])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f798,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f797,f298])).

fof(f298,plain,
    ( k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0)
    | ~ spl2_13 ),
    inference(resolution,[],[f280,f34])).

fof(f280,plain,
    ( v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl2_13
  <=> v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f797,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f790,f61])).

fof(f61,plain,(
    sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f36,f29])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f790,plain,
    ( k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0)))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f445,f116])).

fof(f116,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_6
  <=> v1_relat_1(k4_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f445,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | k4_relat_1(k5_relat_1(X2,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X2)) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f440,f96])).

fof(f440,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(X2)
        | k4_relat_1(k5_relat_1(X2,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X2)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f40,f75])).

fof(f75,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f286,plain,
    ( ~ spl2_4
    | ~ spl2_6
    | spl2_11 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_6
    | spl2_11 ),
    inference(subsumption_resolution,[],[f284,f116])).

fof(f284,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | ~ spl2_4
    | spl2_11 ),
    inference(subsumption_resolution,[],[f282,f75])).

fof(f282,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(sK0))
    | spl2_11 ),
    inference(resolution,[],[f271,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f271,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl2_11
  <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f281,plain,
    ( spl2_13
    | ~ spl2_11
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f276,f115,f73,f269,f278])).

fof(f276,plain,
    ( ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f267,f59])).

fof(f267,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f41,f197])).

fof(f197,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(resolution,[],[f192,f116])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) )
    | ~ spl2_4 ),
    inference(resolution,[],[f190,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f190,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f188,f75])).

fof(f188,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f31])).

fof(f31,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f242,plain,
    ( spl2_1
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl2_1
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f234,f52])).

fof(f52,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_1
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f234,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl2_10 ),
    inference(resolution,[],[f216,f34])).

fof(f216,plain,
    ( v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl2_10
  <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f222,plain,
    ( ~ spl2_4
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl2_4
    | spl2_8 ),
    inference(subsumption_resolution,[],[f220,f29])).

fof(f220,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_4
    | spl2_8 ),
    inference(subsumption_resolution,[],[f218,f75])).

fof(f218,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0)
    | spl2_8 ),
    inference(resolution,[],[f207,f42])).

fof(f207,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl2_8
  <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f217,plain,
    ( spl2_10
    | ~ spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f212,f73,f205,f214])).

fof(f212,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f203,f59])).

fof(f203,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl2_4 ),
    inference(superposition,[],[f41,f199])).

fof(f199,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ spl2_4 ),
    inference(resolution,[],[f192,f29])).

fof(f126,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl2_6 ),
    inference(subsumption_resolution,[],[f123,f29])).

fof(f123,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_6 ),
    inference(resolution,[],[f117,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f117,plain,
    ( ~ v1_relat_1(k4_relat_1(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f81,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f79,f59])).

fof(f79,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_3 ),
    inference(resolution,[],[f77,f33])).

fof(f77,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl2_3 ),
    inference(resolution,[],[f71,f35])).

fof(f71,plain,
    ( ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f76,plain,
    ( ~ spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f67,f73,f69])).

fof(f67,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f35,f66])).

fof(f57,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f28,f54,f50])).

fof(f28,plain,
    ( k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (3345)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.48  % (3327)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (3329)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (3337)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (3349)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (3341)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (3340)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (3328)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (3350)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (3330)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (3334)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (3331)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (3335)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (3343)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (3352)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (3347)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (3332)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (3349)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f810,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f57,f76,f81,f126,f217,f222,f242,f281,f286,f801])).
% 0.21/0.53  fof(f801,plain,(
% 0.21/0.53    spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_13),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f800])).
% 0.21/0.53  fof(f800,plain,(
% 0.21/0.53    $false | (spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f799,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    spl2_2 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f799,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_13)),
% 0.21/0.53    inference(forward_demodulation,[],[f798,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    k1_xboole_0 = k4_relat_1(k1_xboole_0) | ~spl2_3),
% 0.21/0.53    inference(resolution,[],[f94,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl2_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    v1_relat_1(k4_relat_1(k1_xboole_0)) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    spl2_3 <=> v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl2_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f92,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f46,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f34,f46])).
% 0.21/0.53  % (3342)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v1_xboole_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | v1_xboole_0(k4_relat_1(k1_xboole_0)) | ~spl2_3),
% 0.21/0.53    inference(superposition,[],[f41,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl2_3),
% 0.21/0.53    inference(forward_demodulation,[],[f90,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) | ~spl2_3),
% 0.21/0.53    inference(forward_demodulation,[],[f87,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    k1_xboole_0 = k4_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.53    inference(resolution,[],[f62,f59])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.21/0.53    inference(resolution,[],[f36,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) | ~spl2_3),
% 0.21/0.53    inference(resolution,[],[f37,f70])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).
% 0.21/0.53  fof(f798,plain,(
% 0.21/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k1_xboole_0) | (~spl2_3 | ~spl2_4 | ~spl2_6 | ~spl2_13)),
% 0.21/0.53    inference(forward_demodulation,[],[f797,f298])).
% 0.21/0.53  fof(f298,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(k4_relat_1(sK0),k1_xboole_0) | ~spl2_13),
% 0.21/0.53    inference(resolution,[],[f280,f34])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | ~spl2_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f278])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    spl2_13 <=> v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.53  fof(f797,plain,(
% 0.21/0.53    k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl2_3 | ~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f790,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f36,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    v1_relat_1(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.53    inference(negated_conjecture,[],[f14])).
% 0.21/0.53  fof(f14,conjecture,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.53  fof(f790,plain,(
% 0.21/0.53    k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) | (~spl2_3 | ~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(resolution,[],[f445,f116])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    v1_relat_1(k4_relat_1(sK0)) | ~spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    spl2_6 <=> v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.53  fof(f445,plain,(
% 0.21/0.53    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(X2,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X2))) ) | (~spl2_3 | ~spl2_4)),
% 0.21/0.53    inference(forward_demodulation,[],[f440,f96])).
% 0.21/0.53  fof(f440,plain,(
% 0.21/0.53    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(X2,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X2))) ) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f40,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    v1_relat_1(k1_xboole_0) | ~spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl2_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    ~spl2_4 | ~spl2_6 | spl2_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f285])).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    $false | (~spl2_4 | ~spl2_6 | spl2_11)),
% 0.21/0.53    inference(subsumption_resolution,[],[f284,f116])).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(sK0)) | (~spl2_4 | spl2_11)),
% 0.21/0.53    inference(subsumption_resolution,[],[f282,f75])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(sK0)) | spl2_11),
% 0.21/0.53    inference(resolution,[],[f271,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | spl2_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f269])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    spl2_11 <=> v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    spl2_13 | ~spl2_11 | ~spl2_4 | ~spl2_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f276,f115,f73,f269,f278])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f267,f59])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | v1_xboole_0(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(superposition,[],[f41,f197])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) | (~spl2_4 | ~spl2_6)),
% 0.21/0.53    inference(resolution,[],[f192,f116])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) ) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f190,f141])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(resolution,[],[f45,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f188,f75])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(superposition,[],[f39,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    spl2_1 | ~spl2_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f241])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    $false | (spl2_1 | ~spl2_10)),
% 0.21/0.53    inference(subsumption_resolution,[],[f234,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    spl2_1 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl2_10),
% 0.21/0.53    inference(resolution,[],[f216,f34])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl2_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f214])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    spl2_10 <=> v1_xboole_0(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    ~spl2_4 | spl2_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f221])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    $false | (~spl2_4 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f220,f29])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    ~v1_relat_1(sK0) | (~spl2_4 | spl2_8)),
% 0.21/0.53    inference(subsumption_resolution,[],[f218,f75])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0) | spl2_8),
% 0.21/0.53    inference(resolution,[],[f207,f42])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | spl2_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f205])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    spl2_8 <=> v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    spl2_10 | ~spl2_8 | ~spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f212,f73,f205,f214])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl2_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f203,f59])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | v1_xboole_0(k5_relat_1(sK0,k1_xboole_0)) | ~spl2_4),
% 0.21/0.53    inference(superposition,[],[f41,f199])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) | ~spl2_4),
% 0.21/0.53    inference(resolution,[],[f192,f29])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    spl2_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    $false | spl2_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f29])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ~v1_relat_1(sK0) | spl2_6),
% 0.21/0.53    inference(resolution,[],[f117,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(sK0)) | spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f115])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl2_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    $false | spl2_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f79,f59])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | spl2_3),
% 0.21/0.53    inference(resolution,[],[f77,f33])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ~v1_relat_1(k1_xboole_0) | spl2_3),
% 0.21/0.53    inference(resolution,[],[f71,f35])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ~v1_relat_1(k4_relat_1(k1_xboole_0)) | spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f69])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ~spl2_3 | spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f67,f73,f69])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0))),
% 0.21/0.53    inference(superposition,[],[f35,f66])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ~spl2_1 | ~spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f28,f54,f50])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (3349)------------------------------
% 0.21/0.53  % (3349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3349)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (3349)Memory used [KB]: 11001
% 0.21/0.53  % (3349)Time elapsed: 0.060 s
% 0.21/0.53  % (3349)------------------------------
% 0.21/0.53  % (3349)------------------------------
% 0.21/0.53  % (3339)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (3338)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (3326)Success in time 0.18 s
%------------------------------------------------------------------------------
